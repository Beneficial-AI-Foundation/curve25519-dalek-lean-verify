#!/usr/bin/env python3
"""Remove proofs from Lean files by replacing them with 'sorry'."""

import argparse
import re
from pathlib import Path


def remove_proofs(content: str) -> str:
    """
    Replace all proofs in Lean theorems with 'sorry'.

    Only processes theorems (not lemmas, defs, etc.). Proofs are identified by
    'theorem' followed by ':= by', with content removed until either:
    - End of file
    - A line starting with a non-indented keyword (theorem, def, etc.)

    Args:
        content: The Lean file content as a string

    Returns:
        The modified content with theorem proofs replaced by 'sorry'
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
            # Split the line at ':= by'
            before_proof = line.split(':= by')[0]
            result.append(before_proof + ':= by sorry')
            i += 1
            in_theorem = False  # Done processing this theorem

            # Skip all lines until we hit a top-level declaration
            while i < len(lines):
                current_line = lines[i]

                # Stop at top-level keyword (starting at column 0)
                if re.match(r'^(theorem|lemma|def|instance|structure|class|inductive|axiom|example)\s', current_line):
                    # Don't increment i, we want to process this line
                    break

                # Otherwise skip this line (it's part of the proof, including blank lines)
                i += 1
        else:
            result.append(line)
            i += 1

    return '\n'.join(result)


def process_file(file_path: Path, in_place: bool = False) -> None:
    """
    Process a single Lean file.

    Args:
        file_path: Path to the Lean file
        in_place: If True, modify the file in place. Otherwise, print to stdout.
    """
    content = file_path.read_text()
    modified_content = remove_proofs(content)

    if in_place:
        file_path.write_text(modified_content)
        print(f"Modified: {file_path}")
    else:
        print(modified_content)


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

    for file_path in args.files:
        if not file_path.exists():
            print(f"Error: File not found: {file_path}")
            continue

        if not file_path.suffix == '.lean':
            print(f"Warning: {file_path} doesn't have .lean extension, processing anyway...")

        process_file(file_path, args.in_place)


if __name__ == '__main__':
    main()
