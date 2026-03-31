#!/usr/bin/env python3
"""Compare two functions.json files and produce a markdown status diff.

Used by CI to post PR comments summarizing verification status changes.

Usage:
    python3 scripts/diff_functions.py --old old.json --new new.json
"""

import argparse
import json
import sys
from pathlib import Path


def shorten(lean_name: str) -> str:
    """Strip the crate prefix for a more readable display name."""
    parts = lean_name.split(".")
    if len(parts) > 1 and parts[0] == "curve25519_dalek":
        return ".".join(parts[1:])
    return lean_name


def load_functions(path: Path) -> dict[str, dict]:
    """Load functions.json and return a dict keyed by lean_name."""
    data = json.loads(path.read_text())
    return {fn["lean_name"]: fn for fn in data.get("functions", [])}


def status_label(fn: dict) -> str:
    """Return a single status label for a function record."""
    if fn.get("verified") and not fn.get("externally_verified"):
        return "verified"
    if fn.get("externally_verified"):
        return "externally_verified"
    if fn.get("specified"):
        return "specified"
    return "unspecified"


def is_visible(fn: dict) -> bool:
    return not fn.get("is_hidden") and not fn.get("is_extraction_artifact")


def count_stats(fns: dict[str, dict]) -> dict[str, int]:
    visible = {k: v for k, v in fns.items() if is_visible(v)}
    return {
        "total": len(visible),
        "specified": sum(1 for f in visible.values() if f.get("specified")),
        "verified": sum(
            1 for f in visible.values()
            if f.get("verified") and not f.get("externally_verified")
        ),
        "externally_verified": sum(
            1 for f in visible.values() if f.get("externally_verified")
        ),
    }


def diff_functions(old_path: Path, new_path: Path) -> str:
    old_fns = load_functions(old_path)
    new_fns = load_functions(new_path)

    status_changes: list[tuple[str, str, str]] = []
    added: list[str] = []
    removed: list[str] = []

    all_names = sorted(set(old_fns) | set(new_fns))

    for name in all_names:
        old_fn = old_fns.get(name)
        new_fn = new_fns.get(name)

        if old_fn is None and new_fn is not None:
            if is_visible(new_fn):
                added.append(name)
            continue
        if new_fn is None and old_fn is not None:
            if is_visible(old_fn):
                removed.append(name)
            continue

        if not is_visible(old_fn) and not is_visible(new_fn):
            continue

        old_status = status_label(old_fn)
        new_status = status_label(new_fn)
        if old_status != new_status:
            status_changes.append((name, old_status, new_status))

    old_stats = count_stats(old_fns)
    new_stats = count_stats(new_fns)

    lines: list[str] = []
    lines.append("## Verification Status Diff\n")

    if not status_changes and not added and not removed:
        lines.append("No verification status changes detected.\n")
    else:
        if status_changes:
            lines.append("### Status Changes\n")
            lines.append("| Function | Before | After |")
            lines.append("|----------|--------|-------|")
            for name, old_s, new_s in status_changes:
                lines.append(f"| `{shorten(name)}` | {old_s} | {new_s} |")
            lines.append("")

        if added:
            lines.append(f"### Added ({len(added)} functions)\n")
            for name in added[:20]:
                lines.append(f"- `{shorten(name)}`")
            if len(added) > 20:
                lines.append(f"- ... and {len(added) - 20} more")
            lines.append("")

        if removed:
            lines.append(f"### Removed ({len(removed)} functions)\n")
            for name in removed[:20]:
                lines.append(f"- `{shorten(name)}`")
            if len(removed) > 20:
                lines.append(f"- ... and {len(removed) - 20} more")
            lines.append("")

    lines.append("### Summary\n")
    lines.append("| Metric | Base | PR | Delta |")
    lines.append("|--------|------|----|-------|")
    for key in ("total", "verified", "externally_verified", "specified"):
        old_v = old_stats[key]
        new_v = new_stats[key]
        delta = new_v - old_v
        sign = "+" if delta > 0 else ""
        label = key.replace("_", " ").title()
        lines.append(f"| {label} | {old_v} | {new_v} | {sign}{delta} |")
    lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", required=True, type=Path, help="Baseline functions.json")
    parser.add_argument("--new", required=True, type=Path, help="PR functions.json")
    args = parser.parse_args()

    if not args.old.exists():
        print("## Verification Status Diff\n")
        print("No baseline available for comparison (first run on this branch).\n")
        sys.exit(0)

    if not args.new.exists():
        print("## Verification Status Diff\n")
        print("Error: new functions.json not found.\n", file=sys.stderr)
        sys.exit(1)

    print(diff_functions(args.old, args.new))


if __name__ == "__main__":
    main()
