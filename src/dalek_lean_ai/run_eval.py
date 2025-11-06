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


@task
def evaluate_lean_fixing():
    lean_agent = react(
        description="Expert Lean theorem prover",
        prompt="""
        You are an expert in the Lean theorem prover.
        Your task is to fix Lean files by replacing 'sorry' statements with valid proofs.

        The working directory is /workspace/curve25519-dalek-lean-verify which contains a Lean project.

        Follow these steps:
        1. Run `lake build` to see the current state of the project
        2. Examine the specific file mentioned in the task that needs to be fixed
        3. Replace each 'sorry' with a complete proof
        4. Run `lake build` again to verify your proofs
        5. If there are still errors or sorries, fix them and repeat

        When you're done, make sure `lake build` succeeds.
        Then verify that the specific file no longer contains any 'sorry' statements.

        Your final response should not use sorries or axioms.
        """,
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
