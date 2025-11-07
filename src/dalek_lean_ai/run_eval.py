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

# Load the prompt from file
_prompt_file = Path(__file__).parent / "lean_agent_prompt.txt"
_LEAN_AGENT_PROMPT = _prompt_file.read_text()


@task
def evaluate_lean_fixing():
    lean_agent = react(
        description="Expert Lean theorem prover",
        prompt=_LEAN_AGENT_PROMPT,
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
