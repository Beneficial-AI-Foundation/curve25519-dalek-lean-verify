#!/usr/bin/env python3
"""
Generate Status Report from CSV

This script reads status.csv and generates a nicely formatted status.md
with proper validation and symbol mapping for extraction and verification states.
"""

import csv
import sys
from pathlib import Path
from typing import Dict, Tuple

# Configuration
CSV_FILE = "status.csv"
OUTPUT_FILE = "status.md"

# Valid values for columns
VALID_EXTRACTED = {"", "extracted"}
VALID_VERIFIED = {"", "draft spec", "specified", "verified"}

# Symbol mappings
EXTRACTED_SYMBOLS = {
    "extracted": "✅",
    "": "☐"
}

VERIFIED_SYMBOLS = {
    "draft spec": "✏️",
    "specified": "📋",
    "verified": "✅",
    "": "☐"
}


def validate_row(row_num: int, extracted: str, verified: str) -> None:
    """Validate CSV row values and raise error if invalid."""
    if extracted not in VALID_EXTRACTED:
        raise ValueError(
            f"Error on row {row_num}: Invalid 'extracted' value '{extracted}'. "
            f"Must be empty or 'extracted'"
        )

    if verified not in VALID_VERIFIED:
        raise ValueError(
            f"Error on row {row_num}: Invalid 'verified' value '{verified}'. "
            f"Must be empty, 'draft spec', 'specified', or 'verified'"
        )


def parse_csv() -> Tuple[list, Dict[str, int]]:
    """Parse CSV file and return rows and statistics."""
    rows = []
    stats = {
        "total": 0,
        "extracted": 0,
        "draft_spec": 0,
        "specified": 0,
        "verified": 0,
        "pending": 0
    }

    with open(CSV_FILE, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)

        for idx, row in enumerate(reader, start=2):  # Start at 2 (header is line 1)
            # Skip empty rows
            if not row.get('function', '').strip():
                continue

            # Extract and normalize values
            function = row.get('function', '').strip()
            source = row.get('source', '').strip()
            lines = row.get('lines', '').strip()  # New column for line numbers
            spec_theorem = row.get('spec_theorem', '').strip()
            extracted = row.get('extracted', '').strip()
            verified = row.get('verified', '').strip()
            notes = row.get('notes', '').strip()

            # Validate
            validate_row(idx, extracted, verified)

            # Update statistics
            stats["total"] += 1

            if extracted == "extracted":
                stats["extracted"] += 1

            if verified == "draft spec":
                stats["draft_spec"] += 1
            elif verified == "specified":
                stats["specified"] += 1
            elif verified == "verified":
                stats["verified"] += 1
            else:  # empty
                stats["pending"] += 1

            # Store row data
            rows.append({
                'function': function,
                'source': source,
                'lines': lines,
                'spec_theorem': spec_theorem,
                'extracted': extracted,
                'verified': verified,
                'notes': notes
            })

    return rows, stats


def format_source_link(source: str, lines: str) -> str:
    """Format source path and line numbers as markdown link."""
    if not source:
        return "-"

    # Remove curve25519-dalek/src/ prefix for display
    source_display = source.replace('curve25519-dalek/src/', '')

    # Combine source path with line numbers for the link
    if lines:
        # Convert L123-L456 to #L123-L456 for GitHub/VSCode linking
        line_anchor = '#' + lines
        source_link_path = source + line_anchor
    else:
        source_link_path = source

    return f"[{source_display}]({source_link_path})"


def format_spec_link(spec_theorem: str) -> str:
    """Format spec theorem path as markdown link."""
    if not spec_theorem:
        return "-"

    # Extract just the filename for display
    spec_display = spec_theorem.split('/')[-1] if '/' in spec_theorem else spec_theorem
    return f"[{spec_display}]({spec_theorem})"


def get_function_name(function: str) -> str:
    """Extract function name (last part after ::)."""
    return function.split('::')[-1] if '::' in function else function


def write_markdown(rows: list, stats: Dict[str, int]) -> None:
    """Write the markdown output file."""
    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        # Header
        f.write("# Verification Status Report\n\n")
        f.write("This document tracks the progress of formally verifying functions from the curve25519-dalek library.\n\n")
        f.write("## Functions\n\n")
        f.write("| Function | Source | Spec Theorem | Extracted | Verified | Notes |\n")
        f.write("|----------|--------|--------------|-----------|----------|-------|\n")

        # Data rows
        for row in rows:
            function_name = get_function_name(row['function'])
            source_link = format_source_link(row['source'], row['lines'])
            spec_link = format_spec_link(row['spec_theorem'])
            extracted_symbol = EXTRACTED_SYMBOLS[row['extracted']]
            verified_symbol = VERIFIED_SYMBOLS[row['verified']]
            notes = row['notes'] if row['notes'] else ""

            f.write(f"| `{function_name}` | {source_link} | {spec_link} | "
                   f"{extracted_symbol} | {verified_symbol} | {notes} |\n")

        # Summary section
        total = stats['total']
        if total > 0:
            extracted_pct = stats['extracted'] * 100 // total
            draft_spec_pct = stats['draft_spec'] * 100 // total
            specified_pct = stats['specified'] * 100 // total
            verified_pct = stats['verified'] * 100 // total
            pending_pct = stats['pending'] * 100 // total
        else:
            extracted_pct = draft_spec_pct = specified_pct = verified_pct = pending_pct = 0

        f.write("\n## Summary\n\n")
        f.write(f"- **Total Functions**: {total}\n")
        f.write(f"- **Extracted**: {stats['extracted']} / {total} ({extracted_pct}%)\n")
        f.write(f"- **Draft Spec**: {stats['draft_spec']} / {total} ({draft_spec_pct}%)\n")
        f.write(f"- **Specified**: {stats['specified']} / {total} ({specified_pct}%)\n")
        f.write(f"- **Verified**: {stats['verified']} / {total} ({verified_pct}%)\n")
        f.write(f"- **Pending**: {stats['pending']} / {total} ({pending_pct}%)\n")

        # Legend
        f.write("\n## Legend\n\n")
        f.write("### Extracted\n")
        f.write("- ✅ Extracted - Function has been successfully extracted to Lean\n")
        f.write("- ☐ Not extracted - Function has not been extracted yet\n")
        f.write("\n")
        f.write("### Verified\n")
        f.write("- ✅ Verified - Function has been formally verified with complete proofs\n")
        f.write("- 📋 Specified - Function has formal specifications but no proofs yet\n")
        f.write("- ✏️ Draft spec - Function has draft natural language specifications\n")
        f.write("- ☐ Not verified - No verification work has been done yet\n")

        # Footer
        f.write("\n---\n\n")
        f.write("*This report is automatically generated from `status.csv`. "
               "Run `./scripts/generate-status.py` to update.*\n")


def main():
    """Main entry point."""
    print("=== Generating Status Report ===")
    print(f"Reading from: {CSV_FILE}")
    print(f"Writing to: {OUTPUT_FILE}")

    # Check if CSV exists
    if not Path(CSV_FILE).exists():
        print(f"Error: {CSV_FILE} not found!")
        sys.exit(1)

    try:
        # Parse CSV
        rows, stats = parse_csv()

        # Write markdown
        write_markdown(rows, stats)

        # Print summary
        print("\n✓ Status report generated successfully!\n")
        print("Summary:")
        print(f"  Total Functions: {stats['total']}")
        print(f"  Extracted: {stats['extracted']} ({stats['extracted'] * 100 // stats['total'] if stats['total'] > 0 else 0}%)")
        print(f"  Draft Spec: {stats['draft_spec']} ({stats['draft_spec'] * 100 // stats['total'] if stats['total'] > 0 else 0}%)")
        print(f"  Specified: {stats['specified']} ({stats['specified'] * 100 // stats['total'] if stats['total'] > 0 else 0}%)")
        print(f"  Verified: {stats['verified']} ({stats['verified'] * 100 // stats['total'] if stats['total'] > 0 else 0}%)")
        print(f"  Pending: {stats['pending']} ({stats['pending'] * 100 // stats['total'] if stats['total'] > 0 else 0}%)")

    except ValueError as e:
        print(f"\n{e}")
        sys.exit(1)
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
