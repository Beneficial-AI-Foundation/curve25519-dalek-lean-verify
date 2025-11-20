import re

from inspect_ai.scorer import Score, accuracy, scorer
from inspect_ai.util import sandbox


@scorer(metrics=[accuracy()])
def lean_proof_scorer():
    async def score(state, target):
        # Get the task_id and target file from the sample metadata
        task_id = state.metadata.get("task_id")
        target_file = state.metadata.get("target_file")

        if not task_id:
            return Score(value=0, explanation="No task_id specified")
        if not target_file:
            return Score(value=0, explanation="No target file specified")

        # Read the file to check the task region
        full_path = f"/workspace/curve25519-dalek-lean-verify/{target_file}"
        file_result = await sandbox().exec(["cat", full_path])
        if not file_result.success:
            return Score(value=0, explanation=f"Could not read file {target_file}")

        file_contents = file_result.stdout

        # Extract the content between the task anchors (handle any indentation)
        pattern = re.compile(
            rf'\s*-- BEGIN TASK {task_id}\n(.*?)\s*-- END TASK {task_id}',
            re.DOTALL
        )
        match = pattern.search(file_contents)

        if not match:
            return Score(value=0, explanation=f"Could not find task {task_id} anchors in {target_file}")

        task_content = match.group(1)

        # Check for cheating: no sorry, no axiom, no task anchors within the proof
        if "sorry" in task_content:
            return Score(value=0, explanation=f"Task {task_id} still contains 'sorry'")
        if "axiom" in task_content:
            return Score(value=0, explanation=f"Task {task_id} contains 'axiom' (cheating)")
        if "-- BEGIN TASK" in task_content or "-- END TASK" in task_content:
            return Score(value=0, explanation=f"Task {task_id} contains task anchor comments (cheating)")

        # Run lake build to check if proofs are valid
        build_result = await sandbox().exec(
            ["lake", "build"],
            cwd="/workspace/curve25519-dalek-lean-verify"
        )
        if not build_result.success:
            error_output = ""
            if build_result.stdout:
                error_output += f"stdout: {build_result.stdout}\n"
            if build_result.stderr:
                error_output += f"stderr: {build_result.stderr}"
            return Score(
                value=0, explanation=f"lake build failed:\n{error_output}"
            )

        return Score(
            value=1,
            explanation=f"Task {task_id} completed successfully! Proof content:\n{task_content}"
        )

    return score
