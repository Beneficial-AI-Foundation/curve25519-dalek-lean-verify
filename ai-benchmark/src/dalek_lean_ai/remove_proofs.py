#!/usr/bin/env python3
"""Remove proofs from Lean files by replacing them with 'sorry'."""

import argparse
import re
from pathlib import Path


def remove_proofs(content: str, task_counter: int = 1) -> tuple[str, int]:
    """
    Replace all proofs in Lean theorems with 'sorry' wrapped in task markers.

    Only processes theorems (not lemmas, defs, etc.). Proofs are identified by
    'theorem' followed by ':= by', with content removed until either:
    - End of file
    - A line starting with a non-indented keyword (theorem, def, etc.)

    Args:
        content: The Lean file content as a string
        task_counter: Starting task number for this file

    Returns:
        A tuple of (modified content with theorem proofs replaced by numbered sorry, next task counter)
    """
    lines = content.split('\n')
    result = []
    i = 0
    in_theorem = False

    while i < len(lines):
        line = lines[i]

        # Track if we're starting a theorem
        if re.match(r'^theorem\s', line):
            in_theorem = True

        # Reset theorem flag at other top-level declarations
        if re.match(r'^(lemma|def|instance|structure|class|inductive|axiom|example)\s', line):
            in_theorem = False

        # Check if this line contains ':= by' and we're in a theorem
        if ':= by' in line and in_theorem:
            # Split the line at ':= by' and get the indentation
            before_proof = line.split(':= by')[0]
            # Determine the indentation level (add 2 spaces for the proof body)
            indent = len(before_proof) - len(before_proof.lstrip())
            proof_indent = ' ' * (indent + 2)

            result.append(before_proof + ':= by')
            result.append(f'{proof_indent}-- BEGIN task {task_counter}')
            result.append(f'{proof_indent}sorry')
            result.append(f'{proof_indent}-- END task {task_counter}')
            task_counter += 1
            i += 1
            in_theorem = False  # Done processing this theorem

            # Skip all proof lines until we hit a new top-level declaration or end statement
            # Track if we've seen blank lines to preserve them
            seen_blank = False
            while i < len(lines):
                current_line = lines[i]

                # If it's a blank line, note it and skip
                if current_line == '':
                    seen_blank = True
                    i += 1
                    continue

                # Stop at top-level declarations or end statements (at any indentation)
                if re.match(r'^\s*(theorem|lemma|def|instance|structure|class|inductive|axiom|example|end|namespace)\s', current_line):
                    # Add back one blank line if we saw any
                    if seen_blank:
                        result.append('')
                    # Don't increment i, we want to process this line normally
                    break

                # Stop at comments or annotations at column 0 (these are typically between declarations)
                if current_line and not current_line[0].isspace() and (current_line.startswith(('--', '/-', '@['))):
                    # Add back one blank line if we saw any
                    if seen_blank:
                        result.append('')
                    # Don't increment i, we want to process this line normally
                    break

                # Otherwise skip this line (it's part of the proof)
                i += 1

            # If we reached EOF and saw blank lines, add one back
            if i >= len(lines) and seen_blank:
                result.append('')
        else:
            result.append(line)
            i += 1

    return '\n'.join(result), task_counter


def process_file(file_path: Path, in_place: bool = False, task_counter: int = 1) -> int:
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
    modified_content, next_counter = remove_proofs(content, task_counter)

    if in_place:
        if content != modified_content:
            file_path.write_text(modified_content)
            print(f"Modified: {file_path}")
    else:
        print(modified_content)

    return next_counter


def main():
    parser = argparse.ArgumentParser(
        description="Remove proofs from Lean theorems (only) by replacing them with 'sorry'.",
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
