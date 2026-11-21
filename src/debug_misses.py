import json


def main():
    with open("data/answers.json") as f:
        answers = json.load(f)["commits"]

    preds = {}
    with open("predictions.jsonl") as f:
        for line in f:
            if not line.strip(): continue
            d = json.loads(line)
            tests = set()
            for w in d["workers"]:
                tests.update(w)
            preds[d["commit"]] = tests

    with open("data/tests.json") as f:
        test_info = {t["number"]: t for t in json.load(f).get("tests", []) if "number" in t}

    total_misses = 0
    for commit, data in answers.items():
        failing = set(data.get("failing", []))
        predicted = preds.get(commit, set())

        missed = failing - predicted
        if missed:
            total_misses += len(missed)
            print(f"Commit {commit} MISSED {len(missed)} failing tests:")
            for m in missed:
                t_name = test_info[m]["id"]
                print(f"  - {m}: {t_name}")

    if total_misses == 0:
        print("\nSUCCESS: Zero misses! Perfect safety.")
    else:
        print(f"\nWARNING: Total missed failing tests: {total_misses} (Expect severe 300s penalties!)")


if __name__ == "__main__":
    main()