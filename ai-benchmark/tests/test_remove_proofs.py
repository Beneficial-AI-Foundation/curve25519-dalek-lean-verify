#!/usr/bin/env python3
"""Tests for remove_proofs.py"""

from pathlib import Path
import pytest

from dalek_lean_ai.remove_proofs import remove_task_proofs


@pytest.mark.parametrize("test_name", ["", "2"])
def test_remove_proofs(test_name):
    """Test that remove_task_proofs transforms input.lean to match expected.lean"""
    tests_dir = Path(__file__).parent

    input_path = tests_dir / f"input{test_name}.lean"
    expected_path = tests_dir / f"expected{test_name}.lean"

    # Read the input and expected files
    input_content = input_path.read_text()
    expected_content = expected_path.read_text()

    # Apply the transformation
    actual_output, _ = remove_task_proofs(input_content, task_counter=1)

    # Compare the result with expected
    assert actual_output == expected_content, (
        f"Output doesn't match expected.\n\n"
        f"Expected:\n{expected_content}\n\n"
        f"Actual:\n{actual_output}"
    )


