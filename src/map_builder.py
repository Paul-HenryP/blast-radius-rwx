import os
import json
import ast
from collections import defaultdict


def main():
    print("Building AST Dependency Map...")

    # Load all tests
    with open("data/tests.json") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    # Map tests by file
    test_file_to_numbers = defaultdict(list)
    for t in tests:
        test_file_to_numbers[t["file"]].append(t["number"])

    module_to_tests = defaultdict(set)

    # Parse every test file to see what it imports
    for test_file, numbers in test_file_to_numbers.items():
        full_path = os.path.join("sqlglot", test_file)
        if not os.path.exists(full_path):
            continue

        try:
            with open(full_path, "r", encoding="utf-8") as f:
                tree = ast.parse(f.read(), filename=full_path)

            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        if alias.name.startswith("sqlglot"):
                            module_to_tests[alias.name].update(numbers)
                elif isinstance(node, ast.ImportFrom):
                    if node.module and node.module.startswith("sqlglot"):
                        module_to_tests[node.module].update(numbers)
                        # Also track the specific functions/classes imported
                        for alias in node.names:
                            full_module = f"{node.module}.{alias.name}"
                            module_to_tests[full_module].update(numbers)
        except Exception as e:
            print(f"Failed to parse {full_path}: {e}")

    # Convert sets to lists and save as JSON inside the src/ folder so Docker copies it!
    output = {k: list(v) for k, v in module_to_tests.items()}
    with open("src/dependency_map.json", "w") as f:
        json.dump(output, f, indent=2)

    print(f"Generated dependency map with {len(output)} modules mapped to tests.")
    print("Saved to src/dependency_map.json")


if __name__ == "__main__":
    main()