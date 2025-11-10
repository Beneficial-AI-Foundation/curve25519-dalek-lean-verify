#!/usr/bin/env python3
"""Tests for remove_proofs.py"""

from pathlib import Path

from dalek_lean_ai.remove_proofs import remove_proofs


def test_remove_proofs():
    """Test that remove_proofs transforms input.lean to match expected.lean"""
    tests_dir = Path(__file__).parent

    input_path = tests_dir / "input.lean"
    expected_path = tests_dir / "expected.lean"

    # Read the input and expected files
    input_content = input_path.read_text()
    expected_content = expected_path.read_text()

    # Apply the transformation
    actual_output = remove_proofs(input_content)

    # Compare the result with expected
    assert actual_output == expected_content, (
        f"Output doesn't match expected.\n\n"
        f"Expected:\n{expected_content}\n\n"
        f"Actual:\n{actual_output}"
    )


if __name__ == "__main__":
    test_remove_proofs()
    print("✓ Test passed!")
