import re
import subprocess
from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample


def build_dataset():
    # Find project root (where build_docker_image.bash is located)
    project_root = Path(__file__).parent.parent.parent
    build_script = project_root / "build_docker_image.bash"

    subprocess.run([str(build_script)], check=True, cwd=project_root)

    # Read docker image tag from centralized file
    docker_tag = (project_root / "DOCKER_IMAGE_TAG").read_text().strip()

    # Get list of files with task markers from Docker, only in Curve25519Dalek directory
    # Files should have numbered task markers after being processed by remove_proofs.py
    files_with_tasks = subprocess.run(
        ["docker", "run", docker_tag, "bash", "-c",
         "cd /workspace/curve25519-dalek-lean-verify && grep -rE 'BEGIN TASK [0-9]+' --include='*.lean' -l Curve25519Dalek/"],
        capture_output=True,
        check=True,
        text=True,
    ).stdout

    task_files = sorted([f.strip() for f in files_with_tasks.split("\n") if f.strip()])

    # Now extract all task IDs from these files
    samples = []
    for file_path in task_files:
        # Remove leading ./ if present and get relative path
        rel_path = file_path.lstrip("./")

        # Read the file contents from docker
        file_contents = subprocess.run(
            ["docker", "run", docker_tag, "cat", f"/workspace/curve25519-dalek-lean-verify/{rel_path}"],
            capture_output=True,
            check=True,
            text=True,
        ).stdout

        # Find all task IDs in this file
        task_pattern = re.compile(r'-- BEGIN TASK (\d+)')
        for match in task_pattern.finditer(file_contents):
            task_id = int(match.group(1))

            sample = Sample(
                input=f"Fix task {task_id} in the Lean file '{rel_path}' by replacing the 'sorry' with a valid proof.",
                metadata={
                    "task_id": task_id,
                    "target_file": rel_path
                }
            )
            samples.append(sample)

    # Sort samples by task_id to ensure consistent ordering
    samples.sort(key=lambda s: s.metadata["task_id"])

    return MemoryDataset(samples)


if __name__ == "__main__":
    dataset = build_dataset()
    print(f"Found {len(dataset)} tasks:\n")
    for i, sample in enumerate(dataset, 1):
        task_id = sample.metadata.get("task_id")
        target_file = sample.metadata.get("target_file")
        print(f"{i}. Task {task_id} in {target_file}")
