import os
import subprocess
import time
import sys


def main():
    print("Running local evaluation (Fast Dev Mode)...")
    start_time = time.time()

    # Run the predictor locally
    with open("predictions.jsonl", "w") as f:
        subprocess.run([sys.executable, "src/main.py"], stdout=f, env={**os.environ, "PYTHONPATH": "."})

    print(f"Predictions generated in {time.time() - start_time:.2f}s")

    # Run the scorer with the correct 3 arguments: data_dir answers_file predictions_file
    print("\n--- Scoring ---")
    result = subprocess.run(
        [sys.executable, "eval/score.py", "data", "data/answers.json", "predictions.jsonl"],
        capture_output=True, text=True
    )

    print(result.stdout)
    if result.stderr:
        print("ERRORS:", result.stderr)


if __name__ == "__main__":
    main()