#!/usr/bin/env python3
"""Remove proofs from Lean files by replacing them with 'sorry'."""

import argparse
import re
from pathlib import Path


def remove_task_proofs(content: str, task_counter: int) -> tuple[str, int]:
    """
    Replace proofs between -- BEGIN TASK / -- END TASK markers with 'sorry'.

    Handles format: · -- BEGIN TASK
                      proof content
                    -- END TASK

    Replaces proof content with just 'sorry', preserving the cdot and task markers.
    Adds task numbers to the markers.

    Args:
        content: The Lean file content as a string
        task_counter: Starting task number for this file

    Returns:
        A tuple of (modified content, next task counter)
    """
    lines = content.split('\n')
    result = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check if this line contains -- BEGIN TASK (with or without cdot)
        if '-- BEGIN TASK' in line:
            # Check if cdot is on the same line
            if '·' in line:
                # Get the indentation and cdot part
                before_comment = line.split('-- BEGIN TASK')[0]
                indent = len(before_comment) - len(before_comment.lstrip())
                indent_str = ' ' * indent

                # Replace with numbered version, keeping the cdot
                result.append(f'{indent_str}· -- BEGIN TASK {task_counter}')
                result.append(f'{indent_str}  sorry')
            else:
                # No cdot on the BEGIN TASK line
                indent = len(line) - len(line.lstrip())
                indent_str = ' ' * indent
                result.append(f'{indent_str}-- BEGIN TASK {task_counter}')
                result.append(f'{indent_str}sorry')

            i += 1

            # Skip all lines until END TASK
            while i < len(lines):
                current_line = lines[i]

                if '-- END TASK' in current_line:
                    # Get indentation of END TASK line
                    end_indent = len(current_line) - len(current_line.lstrip())
                    end_indent_str = ' ' * end_indent
                    result.append(f'{end_indent_str}-- END TASK {task_counter}')
                    task_counter += 1
                    i += 1
                    break

                i += 1
        else:
            result.append(line)
            i += 1

    return '\n'.join(result), task_counter




def process_file(file_path: Path, in_place: bool, task_counter: int) -> int:
    """
    Process a single Lean file.

    Args:
        file_path: Path to the Lean file
        in_place: If True, modify the file in place. Otherwise, print to stdout.
        task_counter: Starting task number for this file

    Returns:
        The next task counter value
    """
    content = file_path.read_text()
    modified_content, next_counter = remove_task_proofs(content, task_counter)

    if in_place:
        if content != modified_content:
            file_path.write_text(modified_content)
            print(f"Modified: {file_path}")
    else:
        print(modified_content)

    return next_counter


def main():
    parser = argparse.ArgumentParser(
        description="Replace proofs between -- BEGIN TASK / -- END TASK markers with numbered sorry statements.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Print modified content to stdout
  python remove_proofs.py file.lean

  # Modify files in place
  python remove_proofs.py -i file1.lean file2.lean

  # Process multiple files
  python remove_proofs.py *.lean
        """
    )

    parser.add_argument(
        'files',
        nargs='+',
        type=Path,
        help='Lean file(s) to process'
    )

    parser.add_argument(
        '-i', '--in-place',
        action='store_true',
        help='Modify files in place instead of printing to stdout'
    )

    args = parser.parse_args()

    # Sort files for deterministic ordering
    sorted_files = sorted(args.files)

    task_counter = 1
    for file_path in sorted_files:
        if not file_path.exists():
            print(f"Error: File not found: {file_path}")
            continue

        if not file_path.suffix == '.lean':
            print(f"Warning: {file_path} doesn't have .lean extension, processing anyway...")

        task_counter = process_file(file_path, args.in_place, task_counter)


if __name__ == '__main__':
    main()
