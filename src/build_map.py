import json
import os


def main():
    print("Building Lexical Function Map...")
    with open("data/tests.json") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    file_to_tests = {}
    for t in tests:
        file_to_tests.setdefault(t["file"], []).append(t)

    keywords = set()
    # 1. Grab all python file names (e.g. 'tsql', 'eliminate_joins')
    for root, _, files in os.walk("sqlglot/sqlglot"):
        for file in files:
            if file.endswith(".py") and file != "__init__.py":
                keywords.add(file.replace(".py", "").lower())

    # 2. Grab all fixture names (strip trailing 's' to prevent the nwnx bug!)
    for root, _, files in os.walk("sqlglot/tests/fixtures"):
        for file in files:
            if file.endswith(".sql"):
                keywords.add(file.replace(".sql", "").lower().split("__")[0].rstrip('s'))

    keyword_to_tests = {kw: set() for kw in keywords}

    # Parse test files chunk by chunk
    for tfile, tlist in file_to_tests.items():
        try:
            with open(os.path.join("sqlglot", tfile), "r", encoding="utf-8") as f:
                content = f.read()
        except Exception:
            continue

        chunks = content.split("def test_")
        global_chunk = chunks[0].lower()  # Imports and class setup

        for chunk in chunks[1:]:
            chunk_lower = chunk.lower()
            func_name = "test_" + chunk_lower.split("(")[0].strip()

            # Find which test ID this chunk belongs to
            matched_tests = [t for t in tlist if func_name in t["id"].lower()]

            for kw in keywords:
                # If the test function mentions the keyword, map it!
                if kw in chunk_lower or kw in global_chunk:
                    keyword_to_tests[kw].update(t["number"] for t in matched_tests)

    # Save the map for our main pipeline
    output = {k: list(v) for k, v in keyword_to_tests.items() if v}
    with open("src/function_map.json", "w") as f:
        json.dump(output, f)

    print(f"Success! Mapped {len(output)} keywords directly to specific test functions.")


if __name__ == "__main__":
    main()