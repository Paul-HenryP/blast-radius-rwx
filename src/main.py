import os
import json
import glob
import sys


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
    """
    Dynamically finds the mathematically cheapest worker count (1-8).
    Minimizes: max(worker_loads) + (2.0 * num_workers)
    """
    if not tests:
        return []

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
    if not os.path.exists(data_dir):
        data_dir = "./data"

    tests_file = os.path.join(data_dir, "tests.json")
    commits_dir = os.path.join(data_dir, "commits")

    with open(tests_file, "r", encoding="utf-8") as f:
        tests_data = json.load(f)

    tests = [t for t in tests_data.get("tests", []) if "number" in t]

    tests_by_file = {}
    for t in tests:
        t_file = t["file"]
        if t_file not in tests_by_file:
            tests_by_file[t_file] = []
        tests_by_file[t_file].append(t)

    # Core engine tests that break easily when any sub-component is touched
    core_test_files = {
        "tests/test_optimizer.py",
        "tests/test_expressions.py",
        "tests/test_parser.py",
        "tests/test_generator.py",
        "tests/test_executor.py",
        "tests/test_transforms.py",
        "tests/test_schema.py",
        "tests/test_time.py",
        "tests/test_diff.py",
        "tests/test_helper.py"
    }

    patch_files = glob.glob(os.path.join(commits_dir, "*.patch"))

    for patch_path in patch_files:
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        changed_files = get_changed_files(patch_path)

        selected_tests = set()
        run_all = False

        for cfile in changed_files:
            # 1. Test Files & Fixtures
            if cfile.startswith("tests/"):
                if cfile in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[cfile])

                # Map SQL fixtures back to their testing suites (e.g. tests/fixtures/optimizer/X.sql -> test_optimizer.py)
                parts = cfile.split("/")
                if len(parts) >= 3 and parts[1] == "fixtures":
                    target = f"tests/test_{parts[2]}.py"
                    if target in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[target])
                    if parts[2] == "optimizer" and "tests/test_optimizer.py" in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file["tests/test_optimizer.py"])
                continue

            if not cfile.startswith("sqlglot/"):
                continue

            basename = os.path.basename(cfile).replace(".py", "")
            dirname = os.path.dirname(cfile)

            # 2. Root structural files (serde.py, expressions.py, tokens.py) -> Run everything
            if dirname == "sqlglot" or dirname == "sqlglot/dataframe":
                run_all = True
                break

            # 3. Component Files (Dialects, Parsers, Optimizer, Typing) -> Run specific tests + Core tests
            if any(x in dirname for x in ["dialects", "parsers", "optimizer", "typing", "executor"]):
                # Run the safety net
                for ct in core_test_files:
                    if ct in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[ct])

                # Also include specific dialect tests
                if "dialects" in dirname or "parsers" in dirname:
                    targets = [f"tests/dialects/test_{basename}.py", "tests/dialects/test_dialect.py"]
                    for tgt in targets:
                        if tgt in tests_by_file:
                            selected_tests.update(t["number"] for t in tests_by_file[tgt])

            # 4. Catch-all fallback
            else:
                for t_file in tests_by_file:
                    if basename in t_file:
                        selected_tests.update(t["number"] for t in tests_by_file[t_file])

        if run_all or not changed_files:
            final_tests = tests
        else:
            final_tests = [t for t in tests if t["number"] in selected_tests]

        # Avoid the deadly 300s penalty if we failed to select any tests
        if not final_tests and changed_files:
            final_tests = tests

        workers = optimize_workers(final_tests)
        print(json.dumps({"commit": commit_id, "workers": workers}), flush=True)


if __name__ == "__main__":
    main()