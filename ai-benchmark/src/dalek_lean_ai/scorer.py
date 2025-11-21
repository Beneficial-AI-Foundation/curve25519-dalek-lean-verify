from inspect_ai.scorer import Score, accuracy, scorer
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
            error_output = ""
            if build_result.stdout:
                error_output += f"stdout: {build_result.stdout}\n"
            if build_result.stderr:
                error_output += f"stderr: {build_result.stderr}"
            return Score(
                value=0, explanation=f"lake build failed:\n{error_output}"
            )

        # Check if the specific file still contains sorry
        check_sorries = await sandbox().exec(["grep", "-w", "sorry", target_file])
        has_sorries = check_sorries.success  # grep returns success if it finds a match
        check_axioms = await sandbox().exec(["grep", "-w", "axiom", target_file])
        has_axioms = check_axioms.success

        if has_sorries:
            return Score(value=0, explanation=f"The file {target_file} still contains sorries")
        if has_axioms:
            return Score(value=0, explanation=f"The file {target_file} contains axioms")

        # Read the file contents to include in the success message
        file_contents_result = await sandbox().exec(["cat", target_file])
        file_contents = file_contents_result.stdout if file_contents_result.success else "Could not read file"

        return Score(value=1, explanation=f"All proofs are valid. File contents:\n{file_contents}")

    return score
