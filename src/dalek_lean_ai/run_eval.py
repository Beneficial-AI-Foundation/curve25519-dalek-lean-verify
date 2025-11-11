import subprocess
from pathlib import Path

from inspect_ai import Task, task
from inspect_ai.agent import react
from inspect_ai.tool import text_editor, tool
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
        tools=[lake_build(), text_editor()],
        attempts=1000,
    )

    return Task(
        dataset=DATASET,
        solver=lean_agent,
        scorer=lean_proof_scorer(),
        sandbox=("docker", str(_dockerfile_path)),
    )
