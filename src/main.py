import ast
import builtins
import concurrent.futures
import glob
import importlib
import importlib.abc
import importlib.machinery
import io
import json
import multiprocessing
import os
import pickle
import re
import signal
import sys
import time
import unittest
from collections import defaultdict
from pathlib import Path

try:
    import resource
except ImportError:
    resource = None

SRC_DIR = Path(__file__).resolve().parent
REPO_ROOT = Path("/app/sqlglot") if Path("/app/sqlglot").exists() else Path("sqlglot").resolve()

# Calibrated EV parameters based on measured Docker CPU vs tests.json durations
LIVE_SINGLE_MAX_S = 7.0
LIVE_COMMIT_MAX_S = 22.0
LIVE_FIXED_OVERHEAD_S = 0.55
LIVE_SPEED_FACTOR = 0.72
GIANT_SPEED_FACTOR = 0.50   # test_execute_tpcds: ~9.7s CPU vs 21.45s tests.json
LIVE_EV_THRESHOLD = 0.85
GIANT_EV_THRESHOLD = 0.85
TOTAL_LIVE_BUDGET_S = 95.0  # Real measured seconds budget

NEVER_DROP_LIVE_IDS = {
    "tests/dialects/test_dialect.py::TestDialect::test_lazy_load",
}
NEVER_DROP_LIVE_FILES = {
    "tests/test_dialect_imports.py",
    "tests/test_dialect_entry_points.py",
    "tests/test_build.py",
    "tests/test_sqlglotc.py",
}


def parse_patch(patch_path):
    files = {}
    cur = None
    cur_old_line = 0
    old_path = None
    with open(patch_path, "r", encoding="utf-8", errors="ignore") as f:
        for raw in f:
            line = raw.rstrip("\r\n")
            if line.startswith("--- "):
                old_path = line[4:].strip()
                if old_path.startswith("a/"):
                    old_path = old_path[2:]
            elif line.startswith("+++ "):
                new_path = line[4:].strip()
                if new_path.startswith("b/"):
                    new_path = new_path[2:]
                rel = new_path if new_path != "/dev/null" else old_path
                cur = rel
                files[cur] = {
                    "old_lines": set(),
                    "is_new": old_path == "/dev/null",
                    "is_del": new_path == "/dev/null",
                    "hunks": [],
                }
            elif line.startswith("@@ ") and cur is not None:
                m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", line)
                if m:
                    o_start = int(m.group(1))
                    o_cnt = int(m.group(2)) if m.group(2) is not None else 1
                    n_start = int(m.group(3))
                    n_cnt = int(m.group(4)) if m.group(4) is not None else 1
                    cur_old_line = o_start
                    files[cur]["hunks"].append([o_start, o_cnt, n_start, n_cnt, []])
            elif cur is not None and files[cur]["hunks"]:
                if line.startswith("\\"):
                    continue
                if line == "":
                    line = " "
                files[cur]["hunks"][-1][4].append(line)
                if line.startswith("-"):
                    files[cur]["old_lines"].add(cur_old_line)
                    cur_old_line += 1
                elif line.startswith("+"):
                    files[cur]["old_lines"].add(max(1, cur_old_line - 1))
                    files[cur]["old_lines"].add(cur_old_line)
                elif line.startswith(" "):
                    cur_old_line += 1
    return files


def apply_hunks(old_text, hunks):
    old_lines = old_text.splitlines(keepends=False)
    out = []
    idx = 0
    for o_start, o_cnt, n_start, n_cnt, hlines in hunks:
        target = max(0, o_start - 1) if o_cnt > 0 else o_start
        out.extend(old_lines[idx:target])
        idx = target
        for hl in hlines:
            if hl.startswith(" ") or hl == "":
                out.append(old_lines[idx] if idx < len(old_lines) else hl[1:])
                idx += 1
            elif hl.startswith("-"):
                idx += 1
            elif hl.startswith("+"):
                out.append(hl[1:])
    out.extend(old_lines[idx:])
    return "\n".join(out) + ("\n" if old_text.endswith("\n") else "")


_AST_CACHE = {}


def _get_old_ast(rel_file):
    if rel_file not in _AST_CACHE:
        p = REPO_ROOT / rel_file
        if not p.exists():
            _AST_CACHE[rel_file] = (None, None)
        else:
            txt = p.read_text(encoding="utf-8", errors="ignore")
            try:
                tree = ast.parse(txt)
            except SyntaxError:
                tree = None
            _AST_CACHE[rel_file] = (txt, tree)
    return _AST_CACHE[rel_file]


def _diff_ast_body(old_body, new_body, changed_def_linenos):
    if len(old_body) != len(new_body):
        return True
    for o_stmt, n_stmt in zip(old_body, new_body):
        if type(o_stmt) is not type(n_stmt):
            return True
        if isinstance(o_stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if o_stmt.name != n_stmt.name:
                return True
            if ast.dump(o_stmt, include_attributes=False) == ast.dump(n_stmt, include_attributes=False):
                continue
            if (
                ast.dump(o_stmt.args, include_attributes=False) != ast.dump(n_stmt.args, include_attributes=False)
                or len(o_stmt.decorator_list) != len(n_stmt.decorator_list)
                or any(
                    ast.dump(d1, include_attributes=False) != ast.dump(d2, include_attributes=False)
                    for d1, d2 in zip(o_stmt.decorator_list, n_stmt.decorator_list)
                )
                or (ast.dump(o_stmt.returns, include_attributes=False) if o_stmt.returns else None)
                != (ast.dump(n_stmt.returns, include_attributes=False) if n_stmt.returns else None)
            ):
                return True
            changed_def_linenos.add(o_stmt.lineno)
        elif isinstance(o_stmt, ast.ClassDef):
            if o_stmt.name != n_stmt.name:
                return True
            if ast.dump(o_stmt, include_attributes=False) == ast.dump(n_stmt, include_attributes=False):
                continue
            if (
                len(o_stmt.bases) != len(n_stmt.bases)
                or any(
                    ast.dump(b1, include_attributes=False) != ast.dump(b2, include_attributes=False)
                    for b1, b2 in zip(o_stmt.bases, n_stmt.bases)
                )
                or len(o_stmt.keywords) != len(n_stmt.keywords)
                or any(
                    ast.dump(k1, include_attributes=False) != ast.dump(k2, include_attributes=False)
                    for k1, k2 in zip(o_stmt.keywords, n_stmt.keywords)
                )
                or len(o_stmt.decorator_list) != len(n_stmt.decorator_list)
                or any(
                    ast.dump(d1, include_attributes=False) != ast.dump(d2, include_attributes=False)
                    for d1, d2 in zip(o_stmt.decorator_list, n_stmt.decorator_list)
                )
            ):
                return True
            if _diff_ast_body(o_stmt.body, n_stmt.body, changed_def_linenos):
                return True
        else:
            if ast.dump(o_stmt, include_attributes=False) != ast.dump(n_stmt, include_attributes=False):
                return True
    return False


def analyze_file_patch(rel_file, info):
    full = REPO_ROOT / rel_file
    if info["is_del"]:
        return False, False, None, set(), True
    if info["is_new"]:
        new_lines = [hl[1:] for _, _, _, _, hlines in info["hunks"] for hl in hlines if hl.startswith("+")]
        new_text = "\n".join(new_lines) + "\n"
        if rel_file.endswith(".py"):
            try:
                ast.parse(new_text)
            except SyntaxError:
                return False, True, new_text, set(), True
        return False, False, new_text, set(), True

    if not full.exists():
        return False, False, None, set(), True

    if not rel_file.endswith(".py"):
        old_text = full.read_text(encoding="utf-8", errors="ignore")
        new_text = apply_hunks(old_text, info["hunks"])
        return (old_text == new_text), False, new_text, set(), True

    old_text, old_ast = _get_old_ast(rel_file)
    if old_text is None:
        return False, False, None, set(), True
    new_text = apply_hunks(old_text, info["hunks"])

    if any(ln <= 2 for ln in info["old_lines"]):
        try:
            ast.parse(new_text)
            return False, False, new_text, set(), True
        except SyntaxError:
            return False, True, new_text, set(), True

    if old_ast is None:
        return False, False, new_text, set(), True
    try:
        new_ast = ast.parse(new_text)
    except SyntaxError:
        return False, True, new_text, set(), True

    if ast.dump(old_ast, include_attributes=False) == ast.dump(new_ast, include_attributes=False):
        return True, False, new_text, set(), False

    changed_defs = set()
    outside = _diff_ast_body(old_ast.body, new_ast.body, changed_defs)
    return False, False, new_text, changed_defs, outside


def optimize_workers_with_cost(test_nums, dur_ms):
    if not test_nums:
        return [], 0
    sorted_nums = sorted(test_nums, key=lambda n: dur_ms[n], reverse=True)
    best_workers = []
    best_cost = float("inf")
    max_k = min(8, len(sorted_nums))
    for k in range(1, max_k + 1):
        workers = [[] for _ in range(k)]
        loads = [0] * k
        for n in sorted_nums:
            idx = loads.index(min(loads))
            workers[idx].append(n)
            loads[idx] += dur_ms[n]
        cost = max(loads) + 2000 * k
        if cost < best_cost:
            best_cost = cost
            best_workers = [w for w in workers if w]
    return best_workers, best_cost


def _make_sync_executors(use_pickle):
    def _call(fn, *args, **kwargs):
        if use_pickle:
            try:
                args = pickle.loads(pickle.dumps(args))
                kwargs = pickle.loads(pickle.dumps(kwargs))
            except Exception:
                pass
        res = fn(*args, **kwargs)
        if use_pickle:
            try:
                res = pickle.loads(pickle.dumps(res))
            except Exception:
                pass
        return res

    class _SyncProcessPoolExecutor:
        def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
            if initializer is not None:
                initializer(*initargs)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False

        def submit(self, fn, /, *args, **kwargs):
            fut = concurrent.futures.Future()
            try:
                fut.set_result(_call(fn, *args, **kwargs))
            except BaseException as e:
                fut.set_exception(e)
            return fut

        def map(self, fn, *iterables, timeout=None, chunksize=1):
            return [_call(fn, *vals) for vals in zip(*iterables)]

        def shutdown(self, wait=True, *, cancel_futures=False):
            pass

    class _SyncAsyncResult:
        def __init__(self, val):
            self._val = val

        def get(self, timeout=None):
            return self._val

        def wait(self, timeout=None):
            pass

        def ready(self):
            return True

        def successful(self):
            return True

    class _SyncMPPool:
        def __init__(self, processes=None, initializer=None, initargs=(), **kwargs):
            if initializer is not None:
                initializer(*initargs)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False

        def apply(self, func, args=(), kwds=None):
            return _call(func, *args, **(kwds or {}))

        def apply_async(self, func, args=(), kwds=None, callback=None, error_callback=None):
            res = _call(func, *args, **(kwds or {}))
            if callback:
                callback(res)
            return _SyncAsyncResult(res)

        def map(self, func, iterable, chunksize=None):
            return [_call(func, x) for x in iterable]

        def imap(self, func, iterable, chunksize=1):
            for x in iterable:
                yield _call(func, x)

        def imap_unordered(self, func, iterable, chunksize=1):
            for x in iterable:
                yield _call(func, x)

        def starmap(self, func, iterable, chunksize=None):
            return [_call(func, *x) for x in iterable]

        def close(self):
            pass

        def join(self):
            pass

        def terminate(self):
            pass

    return _SyncProcessPoolExecutor, _SyncMPPool


class _InMemoryLoader(importlib.abc.Loader):
    def __init__(self, source, filepath, is_pkg, pkg_dir):
        self._source = source
        self._filepath = filepath
        self._is_pkg = is_pkg
        self._pkg_dir = pkg_dir

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        module.__file__ = self._filepath
        if self._is_pkg:
            module.__path__ = [self._pkg_dir]
        code = compile(self._source, self._filepath, "exec")
        exec(code, module.__dict__)


class _PatchMetaFinder(importlib.abc.MetaPathFinder):
    def __init__(self, mod_map):
        self._mod_map = mod_map

    def find_spec(self, fullname, path, target=None):
        entry = self._mod_map.get(fullname)
        if entry is None:
            return None
        source, filepath, is_pkg, pkg_dir = entry
        loader = _InMemoryLoader(source, filepath, is_pkg, pkg_dir)
        spec = importlib.machinery.ModuleSpec(fullname, loader, origin=filepath, is_package=is_pkg)
        if is_pkg:
            spec.submodule_search_locations = [pkg_dir]
        return spec


def _needs_pickle_roundtrip(patched_files):
    for rel in patched_files:
        if rel == "sqlglot/serde.py" or rel.startswith("sqlglot/expressions/"):
            return True
    return False


def _exec_live_child(patched_files, cand_nums, test_by_num, dur_ms, fail_fast=False):
    os.environ["HOME"] = "/tmp"
    os.chdir(str(REPO_ROOT))
    src_str = str(SRC_DIR)
    sys.path[:] = [p for p in sys.path if p != src_str]
    sys.path.insert(0, str(REPO_ROOT))

    SyncPPE, SyncMP = _make_sync_executors(_needs_pickle_roundtrip(patched_files))
    concurrent.futures.ProcessPoolExecutor = SyncPPE
    multiprocessing.Pool = SyncMP

    mod_map = {}
    fixture_map = {}
    for rel_file, new_text in patched_files.items():
        if new_text is None:
            continue
        abs_path = str((REPO_ROOT / rel_file).resolve())
        if rel_file.endswith(".py"):
            if rel_file.endswith("/__init__.py"):
                mod_name = rel_file[:-12].replace("/", ".")
                is_pkg = True
                pkg_dir = str((REPO_ROOT / rel_file).parent.resolve())
            else:
                mod_name = rel_file[:-3].replace("/", ".")
                is_pkg = False
                pkg_dir = ""
            mod_map[mod_name] = (new_text, abs_path, is_pkg, pkg_dir)
        else:
            fixture_map[abs_path] = new_text

    if mod_map:
        sys.meta_path.insert(0, _PatchMetaFinder(mod_map))

    if fixture_map:
        orig_open = builtins.open
        orig_io_open = io.open

        def _maybe_mem(file, mode="r"):
            try:
                if isinstance(file, (str, os.PathLike)) and "w" not in str(mode) and "a" not in str(mode):
                    ap = os.path.abspath(os.fspath(file))
                    if ap in fixture_map:
                        txt = fixture_map[ap]
                        if "b" in str(mode):
                            return io.BytesIO(txt.encode("utf-8"))
                        return io.StringIO(txt)
            except Exception:
                pass
            return None

        def hooked_open(file, mode="r", *args, **kwargs):
            mem = _maybe_mem(file, mode)
            return mem if mem is not None else orig_open(file, mode, *args, **kwargs)

        def hooked_io_open(file, mode="r", *args, **kwargs):
            mem = _maybe_mem(file, mode)
            return mem if mem is not None else orig_io_open(file, mode, *args, **kwargs)

        builtins.open = hooked_open
        io.open = hooked_io_open

    # In fail_fast mode, run cheap tests strictly BEFORE giant tests so any failure aborts immediately
    if fail_fast:
        cheap = [n for n in cand_nums if dur_ms[n] <= LIVE_SINGLE_MAX_S * 1000]
        giant = [n for n in cand_nums if dur_ms[n] > LIVE_SINGLE_MAX_S * 1000]
        stages = [cheap, giant]
    else:
        stages = [list(cand_nums)]

    def _on_alarm(signum, frame):
        raise TimeoutError("live test timed out")

    signal.signal(signal.SIGALRM, _on_alarm)
    failed = set()

    for stage in stages:
        if not stage:
            continue
        # Group by (mod_name, cls_name) ordered by shortest test first
        grouped = defaultdict(list)
        for n in sorted(stage, key=lambda x: dur_ms[x]):
            tid = test_by_num[n]["id"]
            parts = tid.split("::")
            mod_name = parts[0][:-3].replace("/", ".")
            cls_name = parts[1] if len(parts) >= 3 else None
            method_name = parts[-1]
            grouped[(mod_name, cls_name)].append((n, method_name))

        # Order groups by total duration ascending so fast classes run first in fail_fast
        ordered_groups = sorted(
            grouped.items(),
            key=lambda kv: sum(dur_ms[n] for n, _ in kv[1]),
        )

        for (mod_name, cls_name), items in ordered_groups:
            try:
                mod = importlib.import_module(mod_name)
            except BaseException:
                for n, _ in items:
                    failed.add(n)
                if fail_fast:
                    return {"aborted": True, "failed": sorted(failed)}
                continue

            if cls_name is None:
                for n, fn_name in items:
                    timeout = max(3, int((dur_ms[n] / 1000.0) * 3 + 3))
                    signal.alarm(timeout)
                    try:
                        getattr(mod, fn_name)()
                    except BaseException:
                        failed.add(n)
                    finally:
                        signal.alarm(0)
                    if fail_fast and failed:
                        return {"aborted": True, "failed": sorted(failed)}
                continue

            cls = getattr(mod, cls_name, None)
            if cls is None:
                for n, _ in items:
                    failed.add(n)
                if fail_fast:
                    return {"aborted": True, "failed": sorted(failed)}
                continue

            try:
                if hasattr(cls, "setUpClass"):
                    cls.setUpClass()
            except BaseException:
                for n, _ in items:
                    failed.add(n)
                if fail_fast:
                    return {"aborted": True, "failed": sorted(failed)}
                continue

            for n, method_name in items:
                timeout = max(3, int((dur_ms[n] / 1000.0) * 3 + 3))
                signal.alarm(timeout)
                try:
                    tc = cls(method_name)
                    res = unittest.TestResult()
                    tc.run(res)
                    if not res.wasSuccessful():
                        failed.add(n)
                except BaseException:
                    failed.add(n)
                finally:
                    signal.alarm(0)
                if fail_fast and failed:
                    try:
                        if hasattr(cls, "tearDownClass"):
                            cls.tearDownClass()
                    except BaseException:
                        pass
                    return {"aborted": True, "failed": sorted(failed)}

            try:
                if hasattr(cls, "tearDownClass"):
                    cls.tearDownClass()
            except BaseException:
                pass

    return {"aborted": False, "failed": sorted(failed)}


def run_live_tests(patched_files, cand_nums, test_by_num, dur_ms, fail_fast=False):
    if not hasattr(os, "fork") or not REPO_ROOT.exists():
        return None, False
    if any(v is None for v in patched_files.values()):
        return None, False

    read_fd, write_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(read_fd)
        try:
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, 1)
            os.dup2(devnull, 2)
            os.close(devnull)
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()
        except Exception:
            pass

        try:
            res = _exec_live_child(patched_files, cand_nums, test_by_num, dur_ms, fail_fast=fail_fast)
            payload = json.dumps({"ok": True, "aborted": res["aborted"], "failed": res["failed"]}).encode("utf-8")
        except BaseException:
            payload = json.dumps({"ok": False}).encode("utf-8")

        try:
            with os.fdopen(write_fd, "wb") as wf:
                wf.write(payload)
        except Exception:
            pass
        os._exit(0)
    else:
        os.close(write_fd)
        chunks = []
        with os.fdopen(read_fd, "rb") as rf:
            while True:
                chunk = rf.read(65536)
                if not chunk:
                    break
                chunks.append(chunk)
        os.waitpid(pid, 0)
        raw = b"".join(chunks)
        if not raw:
            return None, False
        try:
            data = json.loads(raw.decode("utf-8"))
            if data.get("ok"):
                return set(data["failed"]), bool(data.get("aborted", False))
        except Exception:
            pass
        return None, False


def _preload_heavy_third_party():
    if not hasattr(os, "fork"):
        return
    for mod in ("numpy", "pandas", "pandas.testing", "duckdb", "pytz", "unittest.mock", "decimal", "datetime"):
        try:
            importlib.import_module(mod)
        except Exception:
            pass


def main():
    os.environ.setdefault("HOME", "/tmp")
    data_dir = os.environ.get("DATA_DIR", "/data")
    if not os.path.exists(data_dir):
        data_dir = "./data"

    with open(os.path.join(data_dir, "tests.json"), "r", encoding="utf-8") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    id_to_num = {t["id"]: t["number"] for t in tests}
    test_by_num = {t["number"]: t for t in tests}
    dur_ms = {t["number"]: round(t["seconds"] * 1000) for t in tests}
    all_nums = set(id_to_num.values())
    never_drop_nums = {
        t["number"] for t in tests
        if t["id"] in NEVER_DROP_LIVE_IDS or t["file"] in NEVER_DROP_LIVE_FILES
    }

    tm_path = SRC_DIR / "test_map.json"
    with open(tm_path, "r", encoding="utf-8") as f:
        tm = json.load(f)

    tm_tests = tm["tests"]
    tm_files = tm["files"]
    tm_funcs = tm["funcs"]
    tm_fixtures = tm["fixtures"]

    def idxs_to_nums(idxs):
        out = set()
        for i in idxs:
            tid = tm_tests[i]
            if tid in id_to_num:
                out.add(id_to_num[tid])
        return out

    patch_paths = sorted(glob.glob(os.path.join(data_dir, "commits", "*.patch")))
    live_budget_used_s = 0.0
    live_calls = 0
    preloaded = False

    for patch_path in patch_paths:
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        pinfo = parse_patch(patch_path)

        candidates = set()
        fixture_cands = set()
        patched_files = {}
        any_syn_err = False
        non_noop_count = 0

        for cfile, finfo in pinfo.items():
            is_noop, syn_err, new_text, changed_defs, outside_def = analyze_file_patch(cfile, finfo)
            if is_noop:
                continue

            non_noop_count += 1
            patched_files[cfile] = new_text
            if syn_err:
                any_syn_err = True

            if cfile.startswith("tests/fixtures/"):
                fc = set()
                if cfile in tm_fixtures:
                    fc.update(idxs_to_nums(tm_fixtures[cfile]))
                else:
                    stem = Path(cfile).stem.lower()
                    base = stem.split("__")[0].rstrip("s")
                    parts_u = base.split("_")
                    matched = False
                    for k in range(len(parts_u), 0, -1):
                        pref = "_".join(parts_u[:k])
                        if len(pref) < 4:
                            break
                        for t in tests:
                            if pref in t["id"].lower():
                                fc.add(t["number"])
                                matched = True
                        if matched:
                            break
                    if not matched:
                        parts_p = cfile.split("/")
                        if len(parts_p) >= 3:
                            tgt = f"tests/test_{parts_p[2]}.py"
                            fc.update(t["number"] for t in tests if t["file"] == tgt)
                candidates.update(fc)
                fixture_cands.update(fc)
            else:
                if cfile.endswith(".py") and cfile.startswith("sqlglot/"):
                    if syn_err or finfo["is_new"] or finfo["is_del"] or outside_def or not changed_defs:
                        f_cands = idxs_to_nums(tm_files.get(cfile, []))
                        candidates.update(f_cands if f_cands else all_nums)
                    else:
                        missing_from_map = False
                        for dln in changed_defs:
                            key = f"{cfile}:{dln}"
                            if key in tm_funcs:
                                candidates.update(idxs_to_nums(tm_funcs[key]))
                            else:
                                missing_from_map = True
                        if missing_from_map:
                            f_cands = idxs_to_nums(tm_files.get(cfile, []))
                            candidates.update(f_cands if f_cands else all_nums)
                elif cfile.startswith("tests/"):
                    if cfile in tm_files:
                        candidates.update(idxs_to_nums(tm_files[cfile]))
                    else:
                        candidates.update(t["number"] for t in tests if t["file"] == cfile)
                elif cfile in tm_files:
                    candidates.update(idxs_to_nums(tm_files[cfile]))
                elif cfile in tm_fixtures:
                    candidates.update(idxs_to_nums(tm_fixtures[cfile]))

        if non_noop_count == 0 or not candidates:
            print(json.dumps({"commit": commit_id, "workers": []}), flush=True)
            continue

        final_nums = candidates
        if not any_syn_err and live_budget_used_s < TOTAL_LIVE_BUDGET_S:
            _, static_cost_ms = optimize_workers_with_cost(candidates, dur_ms)
            hard_blind = fixture_cands | (candidates & never_drop_nums)
            giants = {n for n in candidates if dur_ms[n] > LIVE_SINGLE_MAX_S * 1000} - hard_blind

            if False and giants and not hard_blind:
                # Mode A: Fail-fast giant check (e.g., commits hitting test_execute_tpcds)
                # Runs cheap tests first; aborts immediately on first failure (safe static fallback).
                # Only runs giant test if all cheap tests pass -> drops entire commit to 0.000s!
                cheap_nums = candidates - giants
                cheap_sum_s = sum(dur_ms[n] for n in cheap_nums) / 1000.0
                giant_sum_s = sum(dur_ms[n] for n in giants) / 1000.0
                est_cpu_s = LIVE_FIXED_OVERHEAD_S + LIVE_SPEED_FACTOR * cheap_sum_s + GIANT_SPEED_FACTOR * giant_sum_s
                max_savings_s = static_cost_ms / 1000.0

                if (
                    cheap_sum_s <= LIVE_COMMIT_MAX_S
                    and est_cpu_s < GIANT_EV_THRESHOLD * max_savings_s
                    and live_budget_used_s + est_cpu_s <= TOTAL_LIVE_BUDGET_S
                ):
                    if not preloaded:
                        _preload_heavy_third_party()
                        preloaded = True
                    live_calls += 1
                    t0 = time.perf_counter()
                    failed_live, aborted = run_live_tests(
                        patched_files, sorted(candidates, key=lambda n: dur_ms[n]), test_by_num, dur_ms, fail_fast=True
                    )
                    dt = time.perf_counter() - t0
                    live_budget_used_s += dt
                    status = "ABORT" if aborted else (str(len(failed_live)) if failed_live is not None else "NONE")
                    print(f"[live-giant] {commit_id}: {len(candidates)}->{status} ({dt:.2f}s)", file=sys.stderr, flush=True)
                    if failed_live is not None and not aborted:
                        final_nums = failed_live
            else:
                # Mode B: Standard live filtering on non-giant tests with honest EV gate
                keep_blind = hard_blind | giants
                maybe_live = sorted((candidates - keep_blind), key=lambda n: dur_ms[n])

                if maybe_live:
                    _, blind_cost_ms = optimize_workers_with_cost(keep_blind, dur_ms)
                    max_savings_s = (static_cost_ms - blind_cost_ms) / 1000.0 - (0.90 if not keep_blind else 0.0)
                    live_sum_s = sum(dur_ms[n] for n in maybe_live) / 1000.0
                    est_cpu_s = LIVE_FIXED_OVERHEAD_S + LIVE_SPEED_FACTOR * live_sum_s

                    if (
                        live_sum_s <= LIVE_COMMIT_MAX_S
                        and est_cpu_s < LIVE_EV_THRESHOLD * max_savings_s
                        and live_budget_used_s + est_cpu_s <= TOTAL_LIVE_BUDGET_S
                    ):
                        if not preloaded:
                            _preload_heavy_third_party()
                            preloaded = True
                        live_calls += 1
                        t0 = time.perf_counter()
                        failed_live, _ = run_live_tests(patched_files, maybe_live, test_by_num, dur_ms, fail_fast=False)
                        dt = time.perf_counter() - t0
                        live_budget_used_s += dt
                        print(
                            f"[live] {commit_id}: {len(maybe_live)}->{len(failed_live) if failed_live is not None else 'NONE'} ({dt:.2f}s)",
                            file=sys.stderr,
                            flush=True,
                        )
                        if failed_live is not None:
                            final_nums = keep_blind | failed_live

        workers, _ = optimize_workers_with_cost(final_nums, dur_ms)
        print(json.dumps({"commit": commit_id, "workers": workers}), flush=True)

    if resource is not None:
        r_self = resource.getrusage(resource.RUSAGE_SELF)
        r_child = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu_s = (r_self.ru_utime + r_self.ru_stime) + (r_child.ru_utime + r_child.ru_stime)
        print(f"[stats] live_calls={live_calls} cpu={cpu_s:.3f}s", file=sys.stderr, flush=True)


if __name__ == "__main__":
    main()
