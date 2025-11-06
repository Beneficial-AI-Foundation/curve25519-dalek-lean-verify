import subprocess

from inspect_ai.dataset import MemoryDataset, Sample


def build_dataset():
    subprocess.run(["./build_docker_image.bash"], check=True)
    # Get list of files with sorries from Docker
    files_with_sorries = subprocess.run(
        ["docker", "run", "lean_agent", "bash", "-c",
         "cd /workspace/curve25519-dalek-lean-verify && grep -r 'sorry' --include='*.lean' -l"],
        capture_output=True,
        check=True,
        text=True,
    ).stdout

    sorry_files = sorted([f.strip() for f in files_with_sorries.split("\n") if f.strip()])

    samples = []
    for file_path in sorry_files:
        # Remove leading ./ if present and get relative path
        rel_path = file_path.lstrip("./")

        sample = Sample(
            input=f"Fix the Lean file '{rel_path}' by replacing all 'sorry' statements with valid proofs. Run 'lake build' to check your work. Repeat until there are no more sorries in this file.",
            metadata={"target_file": rel_path}
        )
        samples.append(sample)

    return MemoryDataset(samples)


if __name__ == "__main__":
    dataset = build_dataset()
    print(f"Found {len(dataset)} files with sorries:\n")
    for i, sample in enumerate(dataset, 1):
        target_file = sample.metadata.get("target_file")
        print(f"{i}. {target_file}")
