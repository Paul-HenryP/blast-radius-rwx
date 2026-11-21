import json


def main():
    with open("data/answers.json") as f:
        answers = json.load(f)["commits"]

    with open("data/tests.json") as f:
        tests = {t["number"]: t for t in json.load(f).get("tests", []) if "number" in t}

    print("--- COMMIT ANALYSIS MATRIX ---")
    for commit, data in answers.items():
        failing = data.get("failing", [])

        changed = []
        try:
            with open(f"data/commits/{commit}.patch", errors='ignore') as f:
                for line in f:
                    if line.startswith('--- a/') and 'dev/null' not in line:
                        changed.append(line.strip()[6:])
        except Exception:
            pass

        failing_files = set(tests[num]["file"] for num in failing)
        print(f"\nCommit: {commit}")
        print(f"Changed Files: {changed}")
        print(f"Failed Tests:  {list(failing_files) if failing_files else 'NONE (Safe to run 0 tests)'}")


if __name__ == "__main__":
    main()