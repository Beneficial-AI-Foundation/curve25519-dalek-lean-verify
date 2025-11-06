import subprocess

from inspect_ai import Task, task
from inspect_ai.agent import react
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.scorer import Score, accuracy, scorer
from inspect_ai.tool import bash_session, text_editor
from inspect_ai.util import sandbox


@scorer(metrics=[accuracy()])
def lean_proof_scorer():
    async def score(state, target):
        # Get the target file from the sample metadata
        target_file = state.metadata.get("target_file")
        if not target_file:
            return Score(value=0, explanation="No target file specified")

        # Run lake build to check if proofs are valid
        build_result = await sandbox().exec(["lake", "build"])
        if not build_result.success:
            return Score(
                value=0, explanation=f"lake build failed: {build_result.stderr}"
            )

        # Check if the specific file still contains sorry
        check_sorries = await sandbox().exec(["grep", "-w", "sorry", target_file])
        has_sorries = check_sorries.success  # grep returns success if it finds a match

        if has_sorries:
            return Score(value=0, explanation=f"The file {target_file} still contains sorries")

        return Score(value=1, explanation="All proofs are valid")

    return score


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


DATASET = build_dataset()


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
        """,
        # TODO Should the timeout be larger?
        tools=[bash_session(), text_editor()],
        attempts=3,
    )

    return Task(
        dataset=DATASET,
        solver=lean_agent,
        scorer=lean_proof_scorer(),
        sandbox=("docker", "docker/Dockerfile"),
    )
