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
