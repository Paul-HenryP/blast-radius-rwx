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

    patch_files = glob.glob(os.path.join(data_dir, "commits", "*.patch"))

    for patch_path in patch_files:
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        changed_files = get_changed_files(patch_path)

        relevant_files = [c for c in changed_files if c.startswith("sqlglot/") or c.startswith("tests/")]
        selected_tests = set()
        run_all = False

        for cfile in relevant_files:
            parts = cfile.split("/")

            # 1. Test Files & Surgical SQL Fixtures
            if cfile.startswith("tests/"):
                if cfile in tests_by_file:
                    selected_tests.update(t["number"] for t in tests_by_file[cfile])

                if "fixtures" in parts:
                    fixture_name = parts[-1].replace(".sql", "").lower()
                    # THE FIX: strip trailing 's' to match singular test definitions
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

            basename = os.path.basename(cfile).replace(".py", "")
            dirname = os.path.dirname(cfile)

            # 2. Core Engine Files
            if dirname == "sqlglot" and basename in {
                "serde", "expressions", "tokens", "diff",
                "parser", "generator", "helper", "schema",
                "time", "errors", "jsonpath", "trie"
            }:
                run_all = True
                break

            # 3. Component Dependencies
            if "generators" in dirname:
                targets = [f"tests/dialects/test_{basename}.py", "tests/test_generator.py"]
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

            elif "parsers" in dirname:
                targets = [
                    f"tests/dialects/test_{basename}.py",
                    "tests/test_parser.py",
                    "tests/test_optimizer.py",
                    "tests/test_expressions.py"
                ]
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

            elif "dialects" in dirname:
                targets = [
                    f"tests/dialects/test_{basename}.py",
                    "tests/test_dialect.py",
                    "tests/test_optimizer.py"
                ]
                for tgt in tests_by_file:  # wait, bug in V9? no, loops are safe here
                    pass
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

            elif "optimizer" in dirname:
                targets = [
                    "tests/test_optimizer.py",
                    f"tests/optimizer/test_{basename}.py",
                    "tests/test_executor.py"
                ]
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

            elif "executor" in dirname:
                targets = ["tests/test_executor.py", f"tests/executor/test_{basename}.py"]
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

            else:
                targets = [f"tests/test_{basename}.py", "tests/test_optimizer.py", "tests/test_executor.py"]
                for tgt in targets:
                    if tgt in tests_by_file:
                        selected_tests.update(t["number"] for t in tests_by_file[tgt])

        # 4. Final Selection Logic
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