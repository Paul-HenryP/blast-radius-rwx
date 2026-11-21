#!/usr/bin/env python3
"""
Builds a compact, isolated dependency map for SQLGlot using os.fork() + sys.monitoring.
Forces inner ProcessPoolExecutor / multiprocessing.Pool calls to run synchronously
in-process (with pickle roundtrip) so 100% of worker execution & serde.dump/load are traced.
"""

import json
import os
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path.cwd().resolve()  # /app/sqlglot in Docker
OUTPUT_JSON = REPO_ROOT.parent / "src" / "test_map.json"
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

WORKER_RESULTS = {}
FIRST_ERRORS = []


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


def _record_cls_tree(cls, touched_files):
    if cls is None or not isinstance(cls, type):
        return
    for base in getattr(cls, "__mro__", ()):
        try:
            f = inspect.getsourcefile(base) or inspect.getfile(base)
            if f and f.startswith(PKG_PREFIX):
                touched_files.add(f)
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


class _SyncFuture:
    def __init__(self, fn, *args, **kwargs):
        self._exc = None
        self._res = None
        try:
            self._res = _call_with_pickle(fn, *args, **kwargs)
        except BaseException as e:
            self._exc = e

    def result(self, timeout=None):
        if self._exc is not None:
            raise self._exc
        return self._res

    def exception(self, timeout=None):
        return self._exc

    def done(self):
        return True

    def cancelled(self):
        return False

    def add_done_callback(self, fn):
        fn(self)


class _SyncProcessPoolExecutor:
    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer is not None:
            initializer(*initargs)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False

    def submit(self, fn, /, *args, **kwargs):
        return _SyncFuture(fn, *args, **kwargs)

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
    touched_fixtures = set()

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

    # 3. Hook Dialect.get_or_raise so cached dialects/parsers/generators/typing are ALWAYS recorded
    orig_get_or_raise = None
    DialectCls = None
    try:
        from sqlglot.dialects.dialect import Dialect as DialectCls
        orig_get_or_raise = DialectCls.get_or_raise

        @classmethod
        def hooked_get_or_raise(cls, dialect=None):
            res = orig_get_or_raise.__func__(cls, dialect)
            try:
                d_cls = res if isinstance(res, type) else type(res)
                _record_cls_tree(d_cls, touched_files)
                for attr in ("parser_class", "generator_class", "tokenizer_class", "Parser", "Generator", "Tokenizer"):
                    _record_cls_tree(getattr(d_cls, attr, None), touched_files)
                d_name = getattr(d_cls, "__module__", "").rsplit(".", 1)[-1]
                if d_name:
                    typing_file = REPO_ROOT / "sqlglot" / "typing" / f"{d_name}.py"
                    if typing_file.exists():
                        touched_files.add(str(typing_file))
            except Exception:
                pass
            return res

        DialectCls.get_or_raise = hooked_get_or_raise
    except Exception:
        pass

    # 4. sys.monitoring PY_START for fast file + function (co_firstlineno) tracing
    tool_id = _pick_tool_id()
    sys.monitoring.use_tool_id(tool_id, "blast_mapper")

    def on_py_start(code, instruction_offset):
        fn = code.co_filename
        if fn.startswith(PKG_PREFIX):
            touched_files.add(fn)
            touched_funcs.add((fn, code.co_firstlineno))
        elif fn.startswith(TESTS_PREFIX):
            touched_files.add(fn)
        return sys.monitoring.DISABLE

    sys.monitoring.register_callback(tool_id, sys.monitoring.events.PY_START, on_py_start)
    sys.monitoring.set_events(tool_id, sys.monitoring.events.PY_START)

    builtins.open = hooked_open
    io.open = hooked_io_open
    try:
        runtestprotocol(item, log=False, nextitem=None)
    finally:
        builtins.open = orig_open
        io.open = orig_io_open
        if DialectCls is not None and orig_get_or_raise is not None:
            DialectCls.get_or_raise = orig_get_or_raise
        concurrent.futures.ProcessPoolExecutor = orig_ppe
        multiprocessing.Pool = orig_mp_pool
        for mod, attr, orig in patched_mods:
            setattr(mod, attr, orig)
        sys.monitoring.set_events(tool_id, 0)
        sys.monitoring.free_tool_id(tool_id)

    rel_files = sorted(r for r in (_to_rel(f) for f in touched_files) if r)
    rel_fixtures = sorted(r for r in (_to_rel(f) for f in touched_fixtures) if r)
    rel_funcs = []
    for fn, lineno in touched_funcs:
        r = _to_rel(fn)
        if r:
            rel_funcs.append(f"{r}:{lineno}")
    rel_funcs.sort()
    return rel_files, rel_funcs, rel_fixtures


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

            rel_files, rel_funcs, rel_fixtures = _run_traced(item)
            payload = json.dumps({
                "files": rel_files,
                "funcs": rel_funcs,
                "fixtures": rel_fixtures,
                "err": None,
            }).encode("utf-8")
        except BaseException:
            payload = json.dumps({
                "files": [],
                "funcs": [],
                "fixtures": [],
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
                "fixtures": data.get("fixtures", []),
            }

    item.ihook.pytest_runtest_logfinish(nodeid=item.nodeid, location=item.location)
    return True


def pytest_sessionfinish(session, exitstatus):
    SHARD_DIR.mkdir(parents=True, exist_ok=True)
    with open(SHARD_DIR / f"shard_{os.getpid()}.json", "w", encoding="utf-8") as f:
        json.dump({"results": WORKER_RESULTS, "errors": FIRST_ERRORS}, f)
'''


def main():
    SHARD_DIR.mkdir(parents=True, exist_ok=True)
    for old in SHARD_DIR.glob("*.json"):
        old.unlink()

    (SHARD_DIR / "_trace_plugin.py").write_text(PYTEST_PLUGIN_CODE, encoding="utf-8")

    env = os.environ.copy()
    env["TRACE_REPO_ROOT"] = str(REPO_ROOT)
    env["TRACE_SHARD_DIR"] = str(SHARD_DIR)
    env["PYTHONPATH"] = f"{SHARD_DIR}{os.pathsep}{REPO_ROOT}{os.pathsep}{env.get('PYTHONPATH', '')}"
    env["SQLGLOTRS_TOKENIZER"] = "0"

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

    files_map = defaultdict(list)
    funcs_map = defaultdict(list)
    fixtures_map = defaultdict(list)

    for tid, info in merged.items():
        idx = test_to_idx[tid]
        for f in info["files"]:
            files_map[f].append(idx)
        for fn in info["funcs"]:
            funcs_map[fn].append(idx)
        for fx in info["fixtures"]:
            fixtures_map[fx].append(idx)

    if len(funcs_map) == 0 or len(fixtures_map) == 0:
        raise RuntimeError(
            f"ERROR: Tracing incomplete! files={len(files_map)} funcs={len(funcs_map)} fixtures={len(fixtures_map)}"
        )

    final_map = {
        "tests": all_tests,
        "files": {k: sorted(v) for k, v in sorted(files_map.items())},
        "funcs": {k: sorted(v) for k, v in sorted(funcs_map.items())},
        "fixtures": {k: sorted(v) for k, v in sorted(fixtures_map.items())},
    }

    OUTPUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_JSON.write_text(json.dumps(final_map, separators=(",", ":")), encoding="utf-8")
    size_kb = OUTPUT_JSON.stat().st_size / 1024
    print(
        f"SUCCESS! Traced {len(all_tests)} tests | "
        f"{len(files_map)} files | {len(funcs_map)} funcs | {len(fixtures_map)} fixtures "
        f"({size_kb:.1f} KB) -> {OUTPUT_JSON}",
        flush=True,
    )


if __name__ == "__main__":
    main()