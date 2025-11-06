import subprocess
from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample


def build_dataset():
    # Find project root (where build_docker_image.bash is located)
    project_root = Path(__file__).parent.parent.parent
    build_script = project_root / "build_docker_image.bash"

    subprocess.run([str(build_script)], check=True, cwd=project_root)
    # Get list of files with sorries from Docker, only in Curve25519Dalek directory
    files_with_sorries = subprocess.run(
        ["docker", "run", "lean_agent", "bash", "-c",
         "cd /workspace/curve25519-dalek-lean-verify && grep -r 'sorry' --include='*.lean' -l Curve25519Dalek/"],
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
