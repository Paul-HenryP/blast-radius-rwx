import os
import json


def main():
    with open("data/tests.json") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    test_files = set(t["file"] for t in tests)

    # Read all test contents
    test_contents = {}
    for t_file in test_files:
        full_path = os.path.join("sqlglot", t_file)
        if os.path.exists(full_path):
            with open(full_path, "r", encoding="utf-8", errors="ignore") as f:
                test_contents[t_file] = f.read().lower()

    # Find all python files in sqlglot and map them to tests that mention their name
    inverted_map = {}
    for root, _, files in os.walk("sqlglot/sqlglot"):
        for file in files:
            if file.endswith(".py"):
                basename = file[:-3].lower()
                if basename == "__init__": continue

                matched_tests = []
                for t_file, content in test_contents.items():
                    # If the test code mentions the file's name, or the test file itself is named after it
                    if basename in content or basename in t_file.lower():
                        matched_tests.append(t_file)
                inverted_map[basename] = matched_tests

    with open("src/inverted_map.json", "w") as f:
        json.dump(inverted_map, f)

    print(f"Generated inverted map for {len(inverted_map)} core files.")


if __name__ == "__main__":
    main()