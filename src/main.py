import os
import json
import glob


def get_changed_files_and_lines(patch_path):
    changed_files = set()
    file_lines = {}
    current_file = None
    current_line = 0

    with open(patch_path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if line.startswith('--- a/'):
                current_file = line.strip()[6:]
                if current_file != 'dev/null':
                    changed_files.add(current_file)
                    if current_file not in file_lines:
                        file_lines[current_file] = set()
            elif line.startswith('+++ b/'):
                pass
            elif line.startswith('@@ '):
                try:
                    old_info = line.split(' ')[1]
                    start = int(old_info.split(',')[0].replace('-', ''))
                    current_line = start
                except Exception:
                    pass
            elif current_file and current_file != 'dev/null':
                if line.startswith('-') or line.startswith(' '):
                    file_lines[current_file].add(str(current_line))
                    current_line += 1
                elif line.startswith('+'):
                    pass

    return changed_files, file_lines


def optimize_workers(tests):
    if not tests: return []
    tests_sorted = sorted(tests, key=lambda x: x.get("seconds", 0.0), reverse=True)
    best_workers, best_cost = [], float('inf')
    for num_workers in range(1, 9):
        workers = [[] for _ in range(num_workers)]
        loads = [0.0] * num_workers
        for test in tests_sorted:
            min_idx = loads.index(min(loads))
            workers[min_idx].append(test["number"])
            loads[min_idx] += test.get("seconds", 0.0)
        cost = max(loads) + (2.0 * num_workers)
        if cost < best_cost:
            best_cost = cost
            best_workers = [w for w in workers if w]
    return best_workers


def main():
    data_dir = os.environ.get("DATA_DIR", "/data")
    if not os.path.exists(data_dir): data_dir = "./data"

    with open(os.path.join(data_dir, "tests.json"), "r", encoding="utf-8") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    tests_by_file = {}
    for t in tests:
        tests_by_file.setdefault(t["file"], []).append(t)

    try:
        with open("src/line_cov_map.json", "r") as f:
            line_cov = json.load(f)
    except Exception:
        line_cov = {}

    try:
        with open("src/cov_map.json", "r") as f:
            file_cov = json.load(f)
    except Exception:
        file_cov = {}

    bris_kw = [
        "test_tpcds", "test_tpch", "test_optimize", "test_simplify", "test_execute",
        "test_qualify", "test_pushdown", "test_eliminate", "test_quote_identifiers",
        "test_replace_tables", "test_ref_type", "test_annotate", "test_merge",
        "test_normalize", "test_canonicalize", "test_unnest", "test_isolate"
    ]

    for patch_path in glob.glob(os.path.join(data_dir, "commits", "*.patch")):
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        changed_files, file_lines = get_changed_files_and_lines(patch_path)

        relevant_files = [c for c in changed_files if c.startswith("sqlglot/") or c.startswith("tests/")]
        selected_tests = set()
        run_all = False

        for cfile in relevant_files:
            parts = cfile.split("/")
            basename = os.path.basename(cfile).replace(".py", "")
            dirname = os.path.dirname(cfile)

            # 1. SQL Fixtures
            if cfile.startswith("tests/") and "fixtures" in parts:
                fixture_name = parts[-1].replace(".sql", "").lower().split("__")[0].rstrip('s')
                matched = False
                for t in tests:
                    if fixture_name in t["id"].lower():
                        selected_tests.add(t["number"])
                        matched = True
                if not matched:
                    target = f"tests/test_{parts[-2]}.py"
                    if target in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[target])
                continue

            if cfile.startswith("tests/"):
                if cfile in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[cfile])
                continue

            # 2. Root Engine Breaks
            if dirname == "sqlglot" and basename in {"serde", "expressions", "tokens", "diff"}:
                run_all = True
                break

            # 3. Hybrid Coverage (Line-level -> File-level)
            coverage_found = False
            if cfile in line_cov:
                for lineno in file_lines.get(cfile, set()):
                    if lineno in line_cov[cfile]:
                        coverage_found = True
                        for test_id in line_cov[cfile][lineno]:
                            for t in tests:
                                if test_id in t["id"]:
                                    selected_tests.add(t["number"])

            if not coverage_found and cfile in file_cov:
                coverage_found = True
                for test_id in file_cov[cfile]:
                    for t in tests:
                        if test_id in t["id"]:
                            selected_tests.add(t["number"])

            # 4. MICRO-BRIS (Implicit Fallbacks for Dynamic Imports)
            if "dialects" in dirname or "parsers" in dirname or "generators" in dirname:
                tgt = f"tests/dialects/test_{basename}.py"
                if tgt in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[tgt])
                for t in tests:
                    if ("test_optimizer.py" in t["file"] or "test_executor.py" in t["file"]) and any(
                            kw in t["id"] for kw in bris_kw):
                        selected_tests.add(t["number"])

            elif "optimizer" in dirname:
                for t in tests:
                    # FIX: Include test_executor.py!
                    if ("test_optimizer.py" in t["file"] or "test_executor.py" in t["file"]) and any(
                            kw in t["id"] for kw in bris_kw):
                        selected_tests.add(t["number"])

            elif "executor" in dirname:
                for t in tests:
                    if "test_executor.py" in t["file"] and "test_execute" in t["id"]:
                        selected_tests.add(t["number"])

            elif not coverage_found:
                # Absolute fallback if coverage completely missed this python file
                tgt = f"tests/test_{basename}.py"
                if tgt in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[tgt])

        # 5. Load Balance
        if run_all:
            final_tests = tests
        elif not relevant_files:
            final_tests = []
        else:
            final_tests = [t for t in tests if t["number"] in selected_tests]

        workers = optimize_workers(final_tests)
        print(json.dumps({"commit": commit_id, "workers": workers}), flush=True)


if __name__ == "__main__":
    main()