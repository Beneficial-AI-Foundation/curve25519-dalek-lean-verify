from pathlib import Path

from inspect_ai import Task, task
from inspect_ai.agent import react
from inspect_ai.solver import Generate, Solver, solver
from inspect_ai.tool import bash_session, text_editor
from inspect_ai.util import sandbox

from dalek_lean_ai.dataset import build_dataset
from dalek_lean_ai.scorer import lean_proof_scorer

DATASET = build_dataset()

# Get path to docker directory relative to project root
_project_root = Path(__file__).parent.parent.parent
_docker_dir = _project_root / "docker" / "Dockerfile"

# Load the prompt template from file
_prompt_file = Path(__file__).parent / "lean_agent_prompt.txt"
_LEAN_AGENT_PROMPT_TEMPLATE = _prompt_file.read_text()


@solver
def load_prompt_with_files() -> Solver:
    """Solver that loads files from the sandbox and substitutes them into the prompt."""
    async def solve(state, generate: Generate):
        # Read the files from the docker container
        details_md_result = await sandbox().exec(
            ["cat", "/workspace/curve25519-dalek-lean-verify/site/details.md"]
        )
        if not details_md_result.success:
            raise RuntimeError(
                f"Failed to read details.md: {details_md_result.stderr}"
            )

        base_tutorial_result = await sandbox().exec(
            ["cat", "/workspace/aeneas/tests/lean/BaseTutorial.lean"]
        )
        if not base_tutorial_result.success:
            raise RuntimeError(
                f"Failed to read BaseTutorial.lean: {base_tutorial_result.stderr}"
            )

        # List the aeneas tutorials directory
        aeneas_ls_result = await sandbox().exec(
            ["ls", "-1", "/workspace/aeneas/tests/lean/"]
        )
        if not aeneas_ls_result.success:
            raise RuntimeError(
                f"Failed to list aeneas tutorials directory: {aeneas_ls_result.stderr}"
            )

        # Substitute the files into the prompt template
        prompt = _LEAN_AGENT_PROMPT_TEMPLATE.format(
            DETAILS_MD=details_md_result.stdout,
            BASE_TUTORIAL_LEAN=base_tutorial_result.stdout,
            AENEAS_TUTORIALS_LS=aeneas_ls_result.stdout,
        )

        # Update the state with the new prompt
        state.messages.insert(0, {"role": "system", "content": prompt})

        return state

    return solve


@task
def evaluate_lean_fixing():
    lean_agent = [
        load_prompt_with_files(),
        react(
            description="Expert Lean theorem prover",
            # TODO Should the timeout be larger?
            tools=[bash_session(), text_editor()],
            attempts=3,
        )
    ]

    return Task(
        dataset=DATASET,
        solver=lean_agent,
        scorer=lean_proof_scorer(),
        sandbox=("docker", str(_docker_dir)),
    )
