import re
import subprocess
from pathlib import Path

from inspect_ai import Task, task
from inspect_ai.agent import react
from inspect_ai.tool import tool
from inspect_ai.util import sandbox

from dalek_lean_ai.dataset import build_dataset
from dalek_lean_ai.scorer import lean_proof_scorer

DATASET = build_dataset()

# Get path to Dockerfile relative to project root
_project_root = Path(__file__).parent.parent.parent
_dockerfile_path = _project_root / "Dockerfile"

# Load the prompt template from file
_prompt_file = Path(__file__).parent / "lean_agent_prompt.txt"
_LEAN_AGENT_PROMPT_TEMPLATE = _prompt_file.read_text()


def _load_file_from_docker(image_name: str, file_path: str) -> str:
    """Load a file from a docker image using docker run."""
    result = subprocess.run(
        ["docker", "run", "--rm", image_name, "cat", file_path],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"Failed to read {file_path} from image {image_name}: {result.stderr}"
        )
    return result.stdout


def _get_prompt() -> str:
    """Get the prompt with files loaded from the docker image."""
    image_name = (_project_root / "DOCKER_IMAGE_TAG").read_text().strip()

    # Read the files from the docker image
    details_md = _load_file_from_docker(
        image_name, "/workspace/curve25519-dalek-lean-verify/site/details.md"
    )
    base_tutorial = _load_file_from_docker(
        image_name, "/workspace/aeneas/tests/lean/BaseTutorial.lean"
    )

    # Load square_internal_tutorial from the host filesystem
    square_internal_tutorial_path = Path(__file__).parent / "square_internal_tutorial.md"
    square_internal_tutorial = square_internal_tutorial_path.read_text()

    # List the aeneas tutorials directory
    result = subprocess.run(
        ["docker", "run", "--rm", image_name, "ls", "-1", "/workspace/aeneas/tests/lean/"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"Failed to list aeneas tutorials directory: {result.stderr}"
        )
    aeneas_ls = result.stdout

    # Substitute the files into the prompt template
    return _LEAN_AGENT_PROMPT_TEMPLATE.format(
        DETAILS_MD=details_md,
        BASE_TUTORIAL_LEAN=base_tutorial,
        AENEAS_TUTORIALS_LS=aeneas_ls,
        SQUARE_INTERNAL_TUTORIAL=square_internal_tutorial,
    )


@tool
def view_file():
    async def execute(abs_file_path: str, lines: list[int] | None = None):
        """View the contents of a file or directory in the project.

        Args:
            abs_file_path: Absolute file path to view
            lines: Optional list of two integers [start, end] to show only lines start through end (inclusive).
                  Line numbers are 1-indexed. Example: [10, 19] shows lines 10-19.

        Returns:
            The contents of the file with line numbers, or directory listing.
        """
        # Check if it's a directory
        check_dir = await sandbox().exec(["test", "-d", abs_file_path])
        if check_dir.success:
            # It's a directory, run ls
            result = await sandbox().exec(["ls", "-la", abs_file_path])
            if result.success:
                return result.stdout
            else:
                return f"Error listing directory: {result.stderr}"

        # It's a file, use cat -n to show line numbers
        if lines is not None and len(lines) == 2:
            start, end = lines
            # Use sed to extract specific line range
            result = await sandbox().exec(
                ["bash", "-c", f"cat -n {abs_file_path} | sed -n '{start},{end}p'"]
            )
        else:
            result = await sandbox().exec(["cat", "-n", abs_file_path])

        if result.success:
            return result.stdout
        else:
            return f"Error reading file: {result.stderr}"

    return execute


@tool
def insert_proof():
    async def execute(task_id: int, proof: str):
        """Insert a proof for a specific task by replacing the content between task anchors.

        Args:
            task_id: The task number to insert a proof for (from the task markers)
            proof: The proof code to insert between the task anchors. Do NOT include
                  the task anchor comments (-- BEGIN task N / -- END task N) in your proof.

        Returns:
            Success or error message.
        """
        # Check that the proof doesn't contain anchor comments
        if "-- BEGIN task" in proof or "-- END task" in proof:
            return "Error: Your proof contains task anchor comments. Please submit only the proof code without the anchor markers."

        # Find all files with this task ID
        find_result = await sandbox().exec(
            ["bash", "-c", f"cd /workspace/curve25519-dalek-lean-verify && grep -r 'BEGIN task {task_id}' --include='*.lean' -l Curve25519Dalek/"],
        )

        if not find_result.success or not find_result.stdout.strip():
            return f"Error: Could not find task {task_id} in any file."

        # Should only be one file with this task ID
        target_file = find_result.stdout.strip().split('\n')[0]
        full_path = f"/workspace/curve25519-dalek-lean-verify/{target_file}"

        # Read the current file contents
        read_result = await sandbox().exec(["cat", full_path])
        if not read_result.success:
            return f"Error reading file: {read_result.stderr}"

        file_contents = read_result.stdout

        # Replace content between task anchors (handle any indentation)
        pattern = re.compile(
            rf'(\s*-- BEGIN task {task_id}\n)(.*?)(\s*-- END task {task_id})',
            re.DOTALL
        )

        # Check if pattern exists
        if not pattern.search(file_contents):
            return f"Error: Could not find task {task_id} anchors in {target_file}"

        # Replace the content, preserving the anchors and letting LLM handle indentation
        new_contents = pattern.sub(rf'\g<1>{proof}\n\g<3>', file_contents)

        # Write back to the file
        write_result = await sandbox().exec(
            ["bash", "-c", f"cat > {full_path}"],
            input=new_contents
        )

        if not write_result.success:
            return f"Error writing file: {write_result.stderr}"

        return f"Successfully submitted proof for task {task_id} in {target_file}. Use lake_build to verify it compiles."

    return execute


@tool
def lake_build():
    async def execute():
        """Run lake build to compile the Lean project and check for errors.

        This command builds the entire Lean project in /workspace/curve25519-dalek-lean-verify.
        It will show compilation errors if any exist.
        Use this to verify your proofs are correct.

        Returns:
            The output from lake build, including any error messages.
        """
        result = await sandbox().exec(
            ["lake", "build"],
            cwd="/workspace/curve25519-dalek-lean-verify"
        )
        output = ""
        if result.stdout:
            output += result.stdout
        if result.stderr:
            if output:
                output += "\n"
            output += result.stderr
        return output if output else "Build completed with no output."

    return execute


@task
def evaluate_lean_fixing():
    lean_agent = react(
        description="Expert Lean theorem prover",
        prompt=_get_prompt(),
        # TODO Should the timeout be larger?
        tools=[view_file(), insert_proof(), lake_build()],
        attempts=1000,
    )

    return Task(
        dataset=DATASET,
        solver=lean_agent,
        scorer=lean_proof_scorer(),
        sandbox=("docker", str(_dockerfile_path)),
    )
