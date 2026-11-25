# blast-radius-rwx

Hybrid static and live predictive test selection pipeline built for the **RWX Blast Radius** track of the Builders Buildathon (team: `ConfuciusShips`).

Given a git diff against [`sqlglot`](https://github.com/tobymao/sqlglot) and historical test timings, the container outputs a parallel worker schedule of tests to run—minimizing total `simulated_ci_time + local_cpu_time` while avoiding missed regressions (300 s penalty per missed commit).

> **Note:** This repository is a time-boxed hackathon entry rather than a general-purpose library.

## Approach

1. **Offline dependency mapping (`src/build_test_map.py`, `src/test_map.json.gz`):** Traces `sqlglot`'s test suite via Python `sys.monitoring` to build a compressed index mapping files, functions, executed statements, expression classes, dialect components, and SQL fixtures to individual test IDs.
2. **AST & fixture narrowing (`src/main.py`):** Filters provable no-ops (comments, docstrings, type-only edits, safe identity checks) and narrows class/dict/fixture edits (e.g., `EXPRESSION_METADATA`, `TIME_MAPPING` derived attributes, and `tpc-h`/`tpc-ds` fixture pairs) before falling back to file-level coverage.
3. **EV-gated live verification:** For commits whose remaining candidate set is small enough to be worth verifying locally, forks an isolated worker (`os.fork()` with in-memory module patching via `sys.meta_path`) and drops passing tests only when expected CI savings exceed measured local CPU cost.
   - Calling `gc.freeze()` before `os.fork()` prevented forked workers from scanning hundreds of thousands of cached AST/map objects during tests that invoke `gc.collect()` repeatedly (e.g., `test_generator_memory`), cutting live execution time from ~11 s to ~1.5 s.
4. **Makespan scheduling:** Assigns selected tests across CI workers using LPT bin packing to minimize wall-clock makespan.

## Results (Hidden Leaderboard — Final Submission `5ddaa849be27`)

Evaluated across 3 deterministic runs inside a resource-capped, network-disabled Docker container:

- **Score (median total):** `221.6 s`
- **Simulated CI time:** `206.214 s`
- **Local CPU time:** `15.23 s – 15.38 s`
- **Missed commits:** `0 / 3` runs

## Limitations & Post-Mortem

- **Synthetic vs. real diff distribution:** Optimizing AST micro-rules against a locally generated 53-commit mutant set cut local total time by ~87 s (`254.5 s` → `167.6 s`, 0 misses), but only moved hidden simulated time by ~6 s. Broad multi-line diffs bypass narrow static rules more often than single-line mutations.
- **Pure-Python vs. compiled CI runtime:** Several optimizer tests (`test_simplify`, `test_qualify_columns`, `test_canonicalize`) ran 9x–21x slower in pure Python inside the container than their compiled CI timings, forcing the live-testing gate to treat them as blind-keep and leaving most of the CPU budget unused.

## Repository Layout

- `src/main.py` — Runtime selector, AST analyzers, forked live runner, and worker scheduler.
- `src/build_test_map.py` — Offline coverage/fixture indexer generating `src/test_map.json.gz`.
- `eval/` — Local scoring, mutation generation, and diagnostic scripts.
- `Dockerfile` — Reproducible container environment matching the evaluation harness.

## Usage

```bash
docker build -t blast-radius-rwx .
docker run --rm --network none --read-only \
  --memory=4g --cpus=2.0 --user nobody -e HOME=/tmp \
  --tmpfs /tmp:size=64m,exec,mode=1777 \
  -v /path/to/data:/data:ro \
  blast-radius-rwx
