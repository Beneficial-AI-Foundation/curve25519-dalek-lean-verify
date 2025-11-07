import subprocess
from pathlib import Path

from inspect_ai import Task, task
from inspect_ai.agent import react
from inspect_ai.tool import bash_session, text_editor

from dalek_lean_ai.dataset import build_dataset
from dalek_lean_ai.scorer import lean_proof_scorer

DATASET = build_dataset()

# Get path to docker directory relative to project root
_project_root = Path(__file__).parent.parent.parent
_docker_dir = _project_root / "docker" / "Dockerfile"

# Load the prompt template from file
_prompt_file = Path(__file__).parent / "lean_agent_prompt.txt"
_LEAN_AGENT_PROMPT_TEMPLATE = _prompt_file.read_text()


def _load_file_from_docker(container_name: str, file_path: str) -> str:
    """Load a file from a docker container using docker exec."""
    result = subprocess.run(
        ["docker", "exec", container_name, "cat", file_path],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"Failed to read {file_path} from container {container_name}: {result.stderr}"
        )
    return result.stdout


def _get_prompt() -> str:
    """Get the prompt with files loaded from the docker container."""
    container_name = "lean_agent"

    # Read the files from the docker container
    details_md = _load_file_from_docker(
        container_name, "/workspace/curve25519-dalek-lean-verify/site/details.md"
    )
    base_tutorial = _load_file_from_docker(
        container_name, "/workspace/aeneas/tests/lean/BaseTutorial.lean"
    )

    # List the aeneas tutorials directory
    result = subprocess.run(
        ["docker", "exec", container_name, "ls", "-1", "/workspace/aeneas/tests/lean/"],
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
    )


@task
def evaluate_lean_fixing():
    lean_agent = react(
        description="Expert Lean theorem prover",
        prompt=_get_prompt(),
        # TODO Should the timeout be larger?
        tools=[bash_session(), text_editor()],
        attempts=3,
    )

    return Task(
        dataset=DATASET,
        solver=lean_agent,
        scorer=lean_proof_scorer(),
        sandbox=("docker", str(_docker_dir)),
    )
