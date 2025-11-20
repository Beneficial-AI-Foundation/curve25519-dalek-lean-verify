#!/usr/bin/env python3
"""Remove proofs from Lean files by replacing them with 'sorry'."""

import argparse
import re
from pathlib import Path


def remove_task_proofs(content: str, task_counter: int) -> tuple[str, int]:
    """
    Replace proofs between -- BEGIN TASK / -- END TASK markers with 'sorry'.

    Preserves the cdot (·) and replaces everything after it with sorry.
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

        # Check if this line contains -- BEGIN TASK
        if '-- BEGIN TASK' in line:
            # Get the indentation of this line
            indent = len(line) - len(line.lstrip())
            indent_str = ' ' * indent

            # Replace BEGIN TASK with numbered version
            result.append(f'{indent_str}-- BEGIN task {task_counter}')
            i += 1

            # Find the line with the cdot (·)
            cdot_found = False
            while i < len(lines):
                current_line = lines[i]

                # Check for -- END TASK
                if '-- END TASK' in current_line:
                    # Add the numbered END marker
                    result.append(f'{indent_str}-- END task {task_counter}')
                    task_counter += 1
                    i += 1
                    break

                # Check if this line has a cdot
                if '·' in current_line and not cdot_found:
                    # Extract everything up to and including the cdot
                    cdot_index = current_line.index('·')
                    cdot_indent = len(current_line) - len(current_line.lstrip())
                    cdot_indent_str = ' ' * cdot_indent

                    # Add the cdot line with sorry
                    result.append(f'{cdot_indent_str}· sorry')
                    cdot_found = True
                    i += 1
                    # Skip remaining lines until END TASK
                    continue

                # If we haven't found cdot yet, keep the line
                if not cdot_found:
                    result.append(current_line)

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
