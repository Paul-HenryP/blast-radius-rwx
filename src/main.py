import os
import json
import glob


def get_changed_files(patch_path):
    changed = set()
    with open(patch_path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if line.startswith('--- a/') or line.startswith('+++ b/'):
                filepath = line.strip()[6:]
                if filepath != 'dev/null':
                    changed.add(filepath)
    return changed


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
        tests_data = json.load(f)
    tests = [t for t in tests_data.get("tests", []) if "number" in t]

    tests_by_file = {}
    for t in tests:
        tests_by_file.setdefault(t["file"], []).append(t)

    try:
        with open("src/cov_map.json", "r") as f:
            cov_map = json.load(f)
    except Exception:
        cov_map = {}

    patch_files = glob.glob(os.path.join(data_dir, "commits", "*.patch"))

    volatile_keywords = [
        "test_tpcds", "test_tpch", "test_optimize", "test_simplify",
        "test_qualify_columns", "test_qualify_tables", "test_quote_identifiers",
        "test_replace_tables", "test_ref_type", "test_annotate_funcs",
        "test_execute_subqueries", "test_execute_tpcds",
        "test_pushdown", "test_eliminate", "test_regexp_split",
        "test_information_schema_roundtrip", "test_ml_functions", "test_bigquery",
        "test_clickhouse_values", "test_quoted_identifier_meta"
    ]

    for patch_path in patch_files:
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        changed_files = get_changed_files(patch_path)

        relevant_files = [c for c in changed_files if c.startswith("sqlglot/") or c.startswith("tests/")]
        selected_tests = set()
        run_all = False

        for cfile in relevant_files:
            parts = cfile.split("/")
            basename = os.path.basename(cfile).replace(".py", "")
            dirname = os.path.dirname(cfile)

            # 1. SQL Fixtures
            if cfile.startswith("tests/") and "fixtures" in parts:
                fixture_name = parts[-1].replace(".sql", "").lower()
                base_fixture = fixture_name.split("__")[0].rstrip('s')
                matched = False
                for t in tests:
                    if base_fixture in t["id"].lower():
                        selected_tests.add(t["number"])
                        matched = True
                if not matched:
                    parent_dir = parts[-2]
                    target = f"tests/test_{parent_dir}.py"
                    if target in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[target])
                continue

            # 2. Hardcore Root Files
            if dirname == "sqlglot" and basename in {"serde", "expressions", "tokens", "diff"}:
                run_all = True
                break

            # 3. Dynamic Coverage Map
            if cfile in cov_map:
                for test_id in cov_map[cfile]:
                    for t in tests:
                        if test_id in t["id"]:
                            selected_tests.add(t["number"])

            # 4. Dialect/Generator Bridge
            targets = [f"tests/dialects/test_{basename}.py", f"tests/test_{basename}.py"]
            for tgt in targets:
                if tgt in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[tgt])

            # 5. Blast Radius Integration Suite (BRIS)
            if cfile.startswith("sqlglot/"):
                for t in tests:
                    for kw in volatile_keywords:
                        if kw in t["id"]:
                            selected_tests.add(t["number"])
                            break

        if run_all:
            final_tests = tests
        elif not relevant_files:
            final_tests = []
        else:
            final_tests = [t for t in tests if t["number"] in selected_tests]
            if not final_tests:
                final_tests = tests

        workers = optimize_workers(final_tests)
        print(json.dumps({"commit": commit_id, "workers": workers}), flush=True)


if __name__ == "__main__":
    main()