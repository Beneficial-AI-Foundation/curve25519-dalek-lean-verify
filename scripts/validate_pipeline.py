#!/usr/bin/env python3
"""Compare old (lake exe listfuns) and new (probe pipeline) functions.json
to verify that the CI migration preserves verification stats.

Exit code 0 if verified and specified counts match; 1 otherwise.

Usage:
    python3 scripts/validate_pipeline.py \
        --old functions_old.json \
        --new functions.json \
        [--report validation_report.txt]
"""

import argparse
import json
import sys
from pathlib import Path


def load_json(path: Path) -> dict:
    with open(path) as f:
        return json.load(f)


def is_visible(fn: dict) -> bool:
    return (
        not fn.get("is_hidden")
        and not fn.get("is_extraction_artifact")
    )


def aggregate(functions: list[dict]) -> dict:
    visible = [f for f in functions if is_visible(f)]
    return {
        "total": len(functions),
        "visible": len(visible),
        "verified": sum(1 for f in visible if f.get("verified")),
        "specified": sum(1 for f in visible if f.get("specified")),
        "externally_verified": sum(
            1 for f in visible if f.get("externally_verified")
        ),
        "fully_verified": sum(
            1 for f in visible if f.get("fully_verified")
        ),
    }


COMPARE_FIELDS = [
    "is_hidden", "is_extraction_artifact",
    "specified", "verified", "externally_verified", "fully_verified",
]


def compare(old_fns: list[dict], new_fns: list[dict]) -> str:
    old_by_name = {f["lean_name"]: f for f in old_fns}
    new_by_name = {f["lean_name"]: f for f in new_fns}

    old_agg = aggregate(old_fns)
    new_agg = aggregate(new_fns)

    lines: list[str] = []
    lines.append("=" * 70)
    lines.append("Pipeline Validation Report")
    lines.append("=" * 70)

    # --- Aggregate table ---
    lines.append("")
    lines.append("Aggregate Stats")
    lines.append("-" * 55)
    header = f"{'Metric':<25} {'Old':>8} {'New':>8} {'Delta':>8}  Note"
    lines.append(header)
    lines.append("-" * 55)

    critical_ok = True
    for metric in ["total", "visible", "verified", "specified",
                    "externally_verified", "fully_verified"]:
        o = old_agg[metric]
        n = new_agg[metric]
        delta = n - o
        delta_str = f"{delta:+d}" if delta != 0 else "0"
        note = ""
        if metric in ("verified", "specified") and delta != 0:
            note = "MISMATCH"
            critical_ok = False
        elif delta != 0:
            note = "expected"
        lines.append(f"{metric:<25} {o:>8} {n:>8} {delta_str:>8}  {note}")

    lines.append("-" * 55)
    if critical_ok:
        lines.append("RESULT: PASS -- verified and specified counts match")
    else:
        lines.append("RESULT: FAIL -- critical metric mismatch")

    # --- Functions only in one set ---
    only_old = sorted(set(old_by_name) - set(new_by_name))
    only_new = sorted(set(new_by_name) - set(old_by_name))

    if only_old:
        lines.append("")
        lines.append(f"Functions in old only ({len(only_old)}):")
        for name in only_old:
            fn = old_by_name[name]
            vis = "visible" if is_visible(fn) else "hidden"
            spec = "specified" if fn.get("specified") else ""
            lines.append(f"  {name}  [{vis}] {spec}")

    if only_new:
        lines.append("")
        lines.append(f"Functions in new only ({len(only_new)}):")
        for name in only_new:
            fn = new_by_name[name]
            vis = "visible" if is_visible(fn) else "hidden"
            spec = "specified" if fn.get("specified") else ""
            lines.append(f"  {name}  [{vis}] {spec}")

    # --- Per-function mismatches for common functions ---
    common = sorted(set(old_by_name) & set(new_by_name))
    mismatches: list[str] = []
    for name in common:
        ofn = old_by_name[name]
        nfn = new_by_name[name]
        diffs = []
        for field in COMPARE_FIELDS:
            ov = ofn.get(field)
            nv = nfn.get(field)
            if ov != nv:
                diffs.append(f"{field}: {ov} -> {nv}")
        if diffs:
            mismatches.append(f"  {name}")
            for d in diffs:
                mismatches.append(f"    {d}")

    if mismatches:
        lines.append("")
        lines.append(f"Per-function field mismatches ({len(mismatches)} lines):")
        lines.extend(mismatches)
    else:
        lines.append("")
        lines.append("Per-function field mismatches: none")

    lines.append("")
    return "\n".join(lines), critical_ok


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", required=True, type=Path,
                        help="Baseline functions.json (from lake exe listfuns)")
    parser.add_argument("--new", required=True, type=Path,
                        help="Enriched functions.json (from new pipeline)")
    parser.add_argument("--report", type=Path, default=None,
                        help="Optional file to write the report to")
    args = parser.parse_args()

    old_data = load_json(args.old)
    new_data = load_json(args.new)

    report, ok = compare(old_data["functions"], new_data["functions"])

    print(report)

    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        with open(args.report, "w") as f:
            f.write(report)
        print(f"\nReport saved to {args.report}")

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
