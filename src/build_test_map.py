#!/usr/bin/env python3
"""
Builds a complete, isolated dependency map (v4) for SQLGlot using os.fork() + sys.monitoring.
Outputs gzipped JSON to src/test_map.json.gz containing:
- files:     file-level coverage (including Expr MRO + Dialect MRO + Typing MRO)
- funcs:     function-level coverage with nested-function closure rollup
- lines:     exact per-line coverage inside sqlglot/ (with sync ProcessPoolExecutor)
- exprs:     exact Expression subclass coverage (fixes sqlglot/expressions/*.py blind spots)
- tok_files / par_files / gen_files: component-separated Dialect coverage
- fixtures:  exact tests/fixtures/ usage via open() hooks
"""

import ast
import gzip
import json
import os
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path.cwd().resolve()  # /app/sqlglot in Docker
OUTPUT_GZ = REPO_ROOT.parent / "src" / "test_map.json.gz"
SHARD_DIR = REPO_ROOT / ".trace_shards"

PYTEST_PLUGIN_CODE = r'''
import builtins
import concurrent.futures
import inspect
import io
import json
import multiprocessing
import os
import pickle
import sys
import traceback
from pathlib import Path
import pytest
from _pytest.runner import runtestprotocol

REPO_ROOT = Path(os.environ["TRACE_REPO_ROOT"]).resolve()
REPO_PREFIX = str(REPO_ROOT) + os.sep
PKG_PREFIX = str((REPO_ROOT / "sqlglot").resolve()) + os.sep
TESTS_PREFIX = str((REPO_ROOT / "tests").resolve()) + os.sep
FIXTURES_PREFIX = str((REPO_ROOT / "tests" / "fixtures").resolve()) + os.sep
SHARD_DIR = Path(os.environ["TRACE_SHARD_DIR"])

DIALECTS_INIT = str((REPO_ROOT / "sqlglot" / "dialects" / "__init__.py").resolve())
TYPING_INIT = str((REPO_ROOT / "sqlglot" / "typing" / "__init__.py").resolve())

WORKER_RESULTS = {}
FIRST_ERRORS = []
_CLASS_FILE_CACHE = {}


def _to_rel(path_str):
    if not path_str:
        return None
    try:
        p = Path(path_str).resolve()
        s = str(p)
        if s.startswith(REPO_PREFIX):
            return p.relative_to(REPO_ROOT).as_posix()
    except Exception:
        pass
    return None


def _cls_file(cls):
    if cls in _CLASS_FILE_CACHE:
        return _CLASS_FILE_CACHE[cls]
    res = None
    try:
        f = inspect.getsourcefile(cls) or inspect.getfile(cls)
        if f and f.startswith(PKG_PREFIX):
            res = f
    except Exception:
        pass
    _CLASS_FILE_CACHE[cls] = res
    return res


def _record_cls_tree(cls, *target_sets):
    if cls is None or not isinstance(cls, type):
        return
    for base in getattr(cls, "__mro__", ()):
        f = _cls_file(base)
        if f:
            for s in target_sets:
                s.add(f)


def _record_typing_mro(d_cls, touched_files):
    if d_cls is None or not isinstance(d_cls, type):
        return
    touched_files.add(TYPING_INIT)
    for base in getattr(d_cls, "__mro__", ()):
        try:
            mod_name = getattr(base, "__module__", "")
            if mod_name.startswith("sqlglot.dialects."):
                d_name = mod_name.rsplit(".", 1)[-1]
                tf = REPO_ROOT / "sqlglot" / "typing" / f"{d_name}.py"
                if tf.exists():
                    touched_files.add(str(tf))
        except Exception:
            pass


def _pick_tool_id():
    for tid in range(6):
        if sys.monitoring.get_tool(tid) is None:
            return tid
    return sys.monitoring.PROFILER_ID


def _call_with_pickle(fn, *args, **kwargs):
    try:
        args = pickle.loads(pickle.dumps(args))
        kwargs = pickle.loads(pickle.dumps(kwargs))
    except Exception:
        pass
    res = fn(*args, **kwargs)
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
            fut.set_result(_call_with_pickle(fn, *args, **kwargs))
        except BaseException as e:
            fut.set_exception(e)
        return fut

    def map(self, fn, *iterables, timeout=None, chunksize=1):
        return [_call_with_pickle(fn, *vals) for vals in zip(*iterables)]

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
        return _call_with_pickle(func, *args, **(kwds or {}))

    def apply_async(self, func, args=(), kwds=None, callback=None, error_callback=None):
        res = _call_with_pickle(func, *args, **(kwds or {}))
        if callback:
            callback(res)
        return _SyncAsyncResult(res)

    def map(self, func, iterable, chunksize=None):
        return [_call_with_pickle(func, x) for x in iterable]

    def imap(self, func, iterable, chunksize=1):
        for x in iterable:
            yield _call_with_pickle(func, x)

    def imap_unordered(self, func, iterable, chunksize=1):
        for x in iterable:
            yield _call_with_pickle(func, x)

    def starmap(self, func, iterable, chunksize=None):
        return [_call_with_pickle(func, *x) for x in iterable]

    def close(self):
        pass

    def join(self):
        pass

    def terminate(self):
        pass


def _run_traced(item):
    touched_files = set()
    touched_funcs = set()
    touched_lines = set()
    touched_fixtures = set()
    touched_tok_files = set()
    touched_par_files = set()
    touched_gen_files = set()
    seen_expr_classes = set()

    # 1. Force inner ProcessPoolExecutor / multiprocessing.Pool to run synchronously in-process
    orig_ppe = concurrent.futures.ProcessPoolExecutor
    orig_mp_pool = multiprocessing.Pool
    concurrent.futures.ProcessPoolExecutor = _SyncProcessPoolExecutor
    multiprocessing.Pool = _SyncMPPool
    patched_mods = []
    for mname, mod in list(sys.modules.items()):
        if mod is None:
            continue
        if getattr(mod, "ProcessPoolExecutor", None) is orig_ppe:
            setattr(mod, "ProcessPoolExecutor", _SyncProcessPoolExecutor)
            patched_mods.append((mod, "ProcessPoolExecutor", orig_ppe))
        if getattr(mod, "Pool", None) is orig_mp_pool:
            setattr(mod, "Pool", _SyncMPPool)
            patched_mods.append((mod, "Pool", orig_mp_pool))

    # 2. Hook builtins.open and io.open to capture exact .sql fixture usage
    orig_open = builtins.open
    orig_io_open = io.open

    def _record_open_path(file_arg):
        try:
            if isinstance(file_arg, (str, os.PathLike)):
                p = os.path.abspath(os.fspath(file_arg))
                if p.startswith(FIXTURES_PREFIX):
                    touched_fixtures.add(p)
        except Exception:
            pass

    def hooked_open(file, *args, **kwargs):
        _record_open_path(file)
        return orig_open(file, *args, **kwargs)

    def hooked_io_open(file, *args, **kwargs):
        _record_open_path(file)
        return orig_io_open(file, *args, **kwargs)

    # 3. Hook Expr.__init__ to capture ALL sqlglot/expressions/*.py classes instantiated
    ExprCls = None
    orig_expr_init = None
    try:
        from sqlglot.expressions.core import Expr as ExprCls
        orig_expr_init = ExprCls.__init__

        def hooked_expr_init(self, **args):
            cls = type(self)
            if cls not in seen_expr_classes:
                seen_expr_classes.add(cls)
            orig_expr_init(self, **args)

        ExprCls.__init__ = hooked_expr_init
    except Exception:
        pass

    # 4. Decoupled hooks on Dialect (get_or_raise / parser / generator / tokenizer) & TypeAnnotator
    DialectCls = None
    orig_get_or_raise = None
    orig_parser = None
    orig_generator = None
    orig_tokenizer = None
    TypeAnnotatorCls = None
    orig_ta_init = None

    try:
        from sqlglot.dialects.dialect import Dialect as DialectCls
        orig_get_or_raise = DialectCls.get_or_raise
        orig_parser = DialectCls.parser
        orig_generator = DialectCls.generator
        orig_tokenizer = DialectCls.tokenizer

        @classmethod
        def hooked_get_or_raise(cls, dialect=None):
            res = orig_get_or_raise.__func__(cls, dialect)
            try:
                touched_files.add(DIALECTS_INIT)
                d_cls = res if isinstance(res, type) else type(res)
                _record_cls_tree(d_cls, touched_files)
            except Exception:
                pass
            return res

        def hooked_parser(self, *args, **kwargs):
            p = orig_parser(self, *args, **kwargs)
            try:
                _record_cls_tree(type(self), touched_files)
                _record_cls_tree(type(p), touched_files, touched_par_files)
            except Exception:
                pass
            return p

        def hooked_generator(self, *args, **kwargs):
            g = orig_generator(self, *args, **kwargs)
            try:
                _record_cls_tree(type(self), touched_files)
                _record_cls_tree(type(g), touched_files, touched_gen_files)
            except Exception:
                pass
            return g

        def hooked_tokenizer(self, *args, **kwargs):
            tok = orig_tokenizer(self, *args, **kwargs)
            try:
                _record_cls_tree(type(self), touched_files)
                _record_cls_tree(type(tok), touched_files, touched_tok_files)
            except Exception:
                pass
            return tok

        DialectCls.get_or_raise = hooked_get_or_raise
        DialectCls.parser = hooked_parser
        DialectCls.generator = hooked_generator
        DialectCls.tokenizer = hooked_tokenizer
    except Exception:
        pass

    try:
        from sqlglot.optimizer.annotate_types import TypeAnnotator as TypeAnnotatorCls
        orig_ta_init = TypeAnnotatorCls.__init__

        def hooked_ta_init(self, *args, **kwargs):
            orig_ta_init(self, *args, **kwargs)
            try:
                d = getattr(self, "dialect", None)
                if d is not None:
                    d_cls = d if isinstance(d, type) else type(d)
                    _record_cls_tree(d_cls, touched_files)
                    _record_typing_mro(d_cls, touched_files)
            except Exception:
                pass

        TypeAnnotatorCls.__init__ = hooked_ta_init
    except Exception:
        pass

    # 5. sys.monitoring PY_START + LINE (with DISABLE for low overhead)
    tool_id = _pick_tool_id()
    sys.monitoring.use_tool_id(tool_id, "blast_mapper_v4")

    def on_py_start(code, instruction_offset):
        fn = code.co_filename
        if fn.startswith(PKG_PREFIX):
            touched_files.add(fn)
            touched_funcs.add((fn, code.co_firstlineno))
        elif fn.startswith(TESTS_PREFIX):
            touched_files.add(fn)
        return sys.monitoring.DISABLE

    def on_line(code, lineno):
        fn = code.co_filename
        if fn.startswith(PKG_PREFIX):
            touched_lines.add((fn, lineno))
        return sys.monitoring.DISABLE

    sys.monitoring.register_callback(tool_id, sys.monitoring.events.PY_START, on_py_start)
    sys.monitoring.register_callback(tool_id, sys.monitoring.events.LINE, on_line)
    sys.monitoring.set_events(tool_id, sys.monitoring.events.PY_START | sys.monitoring.events.LINE)

    builtins.open = hooked_open
    io.open = hooked_io_open
    try:
        runtestprotocol(item, log=False, nextitem=None)
    finally:
        sys.monitoring.set_events(tool_id, 0)
        sys.monitoring.free_tool_id(tool_id)
        builtins.open = orig_open
        io.open = orig_io_open
        if ExprCls is not None and orig_expr_init is not None:
            ExprCls.__init__ = orig_expr_init
        if DialectCls is not None:
            if orig_get_or_raise is not None:
                DialectCls.get_or_raise = orig_get_or_raise
            if orig_parser is not None:
                DialectCls.parser = orig_parser
            if orig_generator is not None:
                DialectCls.generator = orig_generator
            if orig_tokenizer is not None:
                DialectCls.tokenizer = orig_tokenizer
        if TypeAnnotatorCls is not None and orig_ta_init is not None:
            TypeAnnotatorCls.__init__ = orig_ta_init
        concurrent.futures.ProcessPoolExecutor = orig_ppe
        multiprocessing.Pool = orig_mp_pool
        for mod, attr, orig in patched_mods:
            setattr(mod, attr, orig)

    # Expand Expr class MROs into files + exprs
    touched_exprs = set()
    for cls in seen_expr_classes:
        for base in getattr(cls, "__mro__", ()):
            f = _cls_file(base)
            if f:
                touched_files.add(f)
                r = _to_rel(f)
                if r:
                    touched_exprs.add(f"{r}:{base.__name__}")

    rel_files = sorted(r for r in (_to_rel(f) for f in touched_files) if r)
    rel_fixtures = sorted(r for r in (_to_rel(f) for f in touched_fixtures) if r)
    rel_tok = sorted(r for r in (_to_rel(f) for f in touched_tok_files) if r)
    rel_par = sorted(r for r in (_to_rel(f) for f in touched_par_files) if r)
    rel_gen = sorted(r for r in (_to_rel(f) for f in touched_gen_files) if r)

    rel_funcs = []
    for fn, lineno in touched_funcs:
        r = _to_rel(fn)
        if r:
            rel_funcs.append(f"{r}:{lineno}")
    rel_funcs.sort()

    rel_lines = {}
    for fn, lineno in touched_lines:
        r = _to_rel(fn)
        if r:
            rel_lines.setdefault(r, []).append(lineno)
    for r in rel_lines:
        rel_lines[r].sort()

    return {
        "files": rel_files,
        "funcs": rel_funcs,
        "lines": rel_lines,
        "exprs": sorted(touched_exprs),
        "tok_files": rel_tok,
        "par_files": rel_par,
        "gen_files": rel_gen,
        "fixtures": rel_fixtures,
    }


@pytest.hookimpl(tryfirst=True)
def pytest_runtest_protocol(item, nextitem):
    item.ihook.pytest_runtest_logstart(nodeid=item.nodeid, location=item.location)
    read_fd, write_fd = os.pipe()
    pid = os.fork()

    if pid == 0:
        os.close(read_fd)
        try:
            import gc
            import functools
            for obj in gc.get_objects():
                if isinstance(obj, functools._lru_cache_wrapper):
                    try:
                        obj.cache_clear()
                    except Exception:
                        pass

            res = _run_traced(item)
            res["err"] = None
            payload = json.dumps(res, separators=(",", ":")).encode("utf-8")
        except BaseException:
            payload = json.dumps({
                "files": [], "funcs": [], "lines": {}, "exprs": [],
                "tok_files": [], "par_files": [], "gen_files": [], "fixtures": [],
                "err": traceback.format_exc(),
            }).encode("utf-8")

        with os.fdopen(write_fd, "wb") as wf:
            wf.write(payload)
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
        if raw:
            data = json.loads(raw.decode("utf-8"))
            if data.get("err") and len(FIRST_ERRORS) < 3:
                FIRST_ERRORS.append(f"{item.nodeid}:\n{data['err']}")
            own_file = _to_rel(str(item.fspath))
            files_set = set(data.get("files", []))
            if own_file:
                files_set.add(own_file)
            WORKER_RESULTS[item.nodeid] = {
                "files": sorted(files_set),
                "funcs": data.get("funcs", []),
                "lines": data.get("lines", {}),
                "exprs": data.get("exprs", []),
                "tok_files": data.get("tok_files", []),
                "par_files": data.get("par_files", []),
                "gen_files": data.get("gen_files", []),
                "fixtures": data.get("fixtures", []),
            }

    item.ihook.pytest_runtest_logfinish(nodeid=item.nodeid, location=item.location)
    return True


def pytest_sessionfinish(session, exitstatus):
    SHARD_DIR.mkdir(parents=True, exist_ok=True)
    with open(SHARD_DIR / f"shard_{os.getpid()}.json", "w", encoding="utf-8") as f:
        json.dump({"results": WORKER_RESULTS, "errors": FIRST_ERRORS}, f, separators=(",", ":"))
'''


def _rollup_nested_funcs(funcs_map):
    """Union every nested def/async def/lambda's test set into its enclosing functions."""
    rolled = 0
    for py_path in sorted((REPO_ROOT / "sqlglot").rglob("*.py")):
        rel = py_path.relative_to(REPO_ROOT).as_posix()
        try:
            tree = ast.parse(py_path.read_text(encoding="utf-8", errors="ignore"))
        except SyntaxError:
            continue
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                okey = f"{rel}:{node.lineno}"
                extra = set()
                for child in ast.walk(node):
                    if child is not node and isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                        ikey = f"{rel}:{child.lineno}"
                        if ikey in funcs_map:
                            extra.update(funcs_map[ikey])
                if extra:
                    before = len(funcs_map.get(okey, set()))
                    funcs_map.setdefault(okey, set()).update(extra)
                    if len(funcs_map[okey]) > before:
                        rolled += 1
    return rolled


def main():
    SHARD_DIR.mkdir(parents=True, exist_ok=True)
    for old in SHARD_DIR.glob("*.json"):
        old.unlink()

    (SHARD_DIR / "_trace_plugin.py").write_text(PYTEST_PLUGIN_CODE, encoding="utf-8")

    env = os.environ.copy()
    env["TRACE_REPO_ROOT"] = str(REPO_ROOT)
    env["TRACE_SHARD_DIR"] = str(SHARD_DIR)
    env["PYTHONPATH"] = f"{SHARD_DIR}{os.pathsep}{REPO_ROOT}{os.pathsep}{env.get('PYTHONPATH', '')}"

    cmd = [sys.executable, "-m", "pytest", "-p", "_trace_plugin", "-q", "-n", "auto"]
    print(f"Running: {' '.join(cmd)}", flush=True)
    proc = subprocess.run(cmd, cwd=REPO_ROOT, env=env)
    print(f"pytest exit code: {proc.returncode}", flush=True)

    merged = {}
    errors = []
    for shard_file in SHARD_DIR.glob("shard_*.json"):
        shard = json.loads(shard_file.read_text(encoding="utf-8"))
        merged.update(shard.get("results", {}))
        errors.extend(shard.get("errors", []))

    if errors:
        print("=== SAMPLE CHILD ERRORS ===", flush=True)
        for e in errors[:3]:
            print(e, flush=True)

    if not merged:
        raise RuntimeError("ERROR: 0 tests were traced! Aborting build.")

    all_tests = sorted(merged.keys())
    test_to_idx = {tid: i for i, tid in enumerate(all_tests)}

    files_map = defaultdict(set)
    funcs_map = defaultdict(set)
    lines_map = defaultdict(lambda: defaultdict(set))
    exprs_map = defaultdict(set)
    tok_map = defaultdict(set)
    par_map = defaultdict(set)
    gen_map = defaultdict(set)
    fixtures_map = defaultdict(set)

    for tid, info in merged.items():
        idx = test_to_idx[tid]
        for f in info["files"]:
            files_map[f].add(idx)
        for fn in info["funcs"]:
            funcs_map[fn].add(idx)
        for rel, lnos in info.get("lines", {}).items():
            fl = lines_map[rel]
            for ln in lnos:
                fl[str(ln)].add(idx)
        for ex in info.get("exprs", []):
            exprs_map[ex].add(idx)
        for f in info.get("tok_files", []):
            tok_map[f].add(idx)
        for f in info.get("par_files", []):
            par_map[f].add(idx)
        for f in info.get("gen_files", []):
            gen_map[f].add(idx)
        for fx in info["fixtures"]:
            fixtures_map[fx].add(idx)

    rolled = _rollup_nested_funcs(funcs_map)
    print(f"Rolled up {rolled} outer functions with nested closures.", flush=True)

    if len(funcs_map) == 0 or len(lines_map) == 0 or len(exprs_map) == 0:
        raise RuntimeError(
            f"ERROR: Tracing incomplete! funcs={len(funcs_map)} lines={len(lines_map)} exprs={len(exprs_map)}"
        )

    final_map = {
        "tests": all_tests,
        "files": {k: sorted(v) for k, v in sorted(files_map.items())},
        "funcs": {k: sorted(v) for k, v in sorted(funcs_map.items())},
        "lines": {
            rel: {ln: sorted(v) for ln, v in sorted(lmap.items(), key=lambda kv: int(kv[0]))}
            for rel, lmap in sorted(lines_map.items())
        },
        "exprs": {k: sorted(v) for k, v in sorted(exprs_map.items())},
        "tok_files": {k: sorted(v) for k, v in sorted(tok_map.items())},
        "par_files": {k: sorted(v) for k, v in sorted(par_map.items())},
        "gen_files": {k: sorted(v) for k, v in sorted(gen_map.items())},
        "fixtures": {k: sorted(v) for k, v in sorted(fixtures_map.items())},
    }

    OUTPUT_GZ.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(OUTPUT_GZ, "wt", encoding="utf-8", compresslevel=6) as gz:
        json.dump(final_map, gz, separators=(",", ":"))

    size_kb = OUTPUT_GZ.stat().st_size / 1024
    total_lines = sum(len(v) for v in final_map["lines"].values())
    print(
        f"SUCCESS! Traced {len(all_tests)} tests | "
        f"{len(files_map)} files | {len(funcs_map)} funcs | {total_lines} lines | "
        f"{len(exprs_map)} exprs | {len(fixtures_map)} fixtures "
        f"({size_kb:.1f} KB gz) -> {OUTPUT_GZ}",
        flush=True,
    )


if __name__ == "__main__":
    main()