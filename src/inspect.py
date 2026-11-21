import os


def main():
    missed = ['3utz', '535z', '986c', 'ary6', 'bvw2', 'j6uz']
    print("--- CHANGED FILES FOR MISSED COMMITS ---")
    for m in missed:
        patch_path = f"data/commits/{m}.patch"
        if not os.path.exists(patch_path):
            continue

        changed_files = set()
        with open(patch_path, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                if line.startswith('--- a/') and 'dev/null' not in line:
                    changed_files.add(line.strip()[6:])

        print(f"\nCommit {m}:")
        for cf in changed_files:
            print(f"  - {cf}")


if __name__ == "__main__":
    main()