#!/usr/bin/env python3
"""
Run extraction experiments with Charon and Aeneas.

This script:
1. Generates rustdoc JSON for a crate
2. Extracts all function/method/constant paths
3. Tests each item with Charon and Aeneas
4. Reports success/failure statistics
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from extract_items import extract_items_from_json


def run_command(cmd, timeout, cwd, debug):
    """
    Run a command with timeout.

    Returns:
        (success: bool, duration: float, stdout: str, stderr: str)
    """
    start = time.time()
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            cwd=cwd,
            timeout=timeout,
            capture_output=True,
            text=True
        )
        duration = time.time() - start

        if debug and (result.stdout or result.stderr):
            print("\n--- STDOUT ---")
            print(result.stdout)
            print("--- STDERR ---")
            print(result.stderr)
            print("--- END ---\n")

        return result.returncode == 0, duration, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        duration = time.time() - start
        if debug:
            print("\n[Command timed out]\n")
        return False, duration, "", ""


def remove_llbc_files(cwd):
    """Remove all .llbc files in the directory."""
    llbc_files = Path(cwd).glob("*.llbc")
    for f in llbc_files:
        f.unlink()


def test_item_extraction(item_path, crate_name, cwd, workspace_root, charon_path, aeneas_path, timeout, debug):
    """
    Test if an item can be extracted with Charon and Aeneas.

    Returns:
        (success: bool, stage: str, duration: float)
        stage is one of: "charon", "aeneas", "success"
    """
    # Remove old LLBC files (in workspace root where charon generates them)
    remove_llbc_files(workspace_root)

    # Run Charon
    charon_cmd = f"{charon_path} cargo --preset=aeneas --start-from '{item_path}' --error-on-warnings -- -p {crate_name}"
    charon_success, charon_duration, _, _ = run_command(charon_cmd, timeout, cwd, debug)

    if not charon_success:
        return False, "charon", charon_duration

    # Run Aeneas (from workspace root where .llbc file is)
    llbc_file = f"{crate_name}.llbc"
    aeneas_cmd = f"{aeneas_path} -backend lean -split-files {llbc_file}"
    aeneas_success, aeneas_duration, _, _ = run_command(aeneas_cmd, timeout, workspace_root, debug)

    total_duration = charon_duration + aeneas_duration

    if not aeneas_success:
        return False, "aeneas", total_duration

    return True, "success", total_duration


def main():
    parser = argparse.ArgumentParser(
        description="Run extraction experiments with Charon and Aeneas"
    )
    parser.add_argument(
        "crate_dir",
        help="Directory containing the Rust crate to test"
    )
    parser.add_argument(
        "--crate-name",
        default="curve25519-dalek",
        help="Name of the crate (default: curve25519-dalek)"
    )
    parser.add_argument(
        "--target-dir",
        help="Target directory for cargo build artifacts (default: <crate_dir>/target)"
    )
    parser.add_argument(
        "--charon",
        default="charon",
        help="Path to charon binary (default: charon from PATH)"
    )
    parser.add_argument(
        "--aeneas",
        default="aeneas",
        help="Path to aeneas binary (default: aeneas from PATH)"
    )
    parser.add_argument(
        "--output",
        help="Output file for results (JSON format)"
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Print stdout/stderr from charon and aeneas commands"
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=10,
        help="Timeout in seconds for charon and aeneas commands (default: 10)"
    )

    args = parser.parse_args()

    crate_dir = Path(args.crate_dir).resolve()
    if not crate_dir.exists():
        print(f"Error: Directory {crate_dir} does not exist", file=sys.stderr)
        sys.exit(1)

    # Determine target directory and workspace root
    if args.target_dir:
        target_dir = Path(args.target_dir).resolve()
    else:
        target_dir = crate_dir / "target"

    workspace_root = target_dir.parent

    print(f"Crate directory: {crate_dir}")
    print(f"Workspace root: {workspace_root}")
    print()

    # Step 1: Generate rustdoc JSON
    print("Step 1: Generating rustdoc JSON...")
    rustdoc_cmd = f"cargo +nightly rustdoc -p {args.crate_name} --all-features -- -Z unstable-options --output-format json"
    success, duration, _, _ = run_command(rustdoc_cmd, 60, crate_dir, args.debug)

    if not success:
        print("Error: Failed to generate rustdoc JSON", file=sys.stderr)
        sys.exit(1)

    print(f"  ✓ Generated in {duration:.2f}s")
    print()

    # Step 2: Extract items
    print("Step 2: Extracting items from rustdoc JSON...")

    json_filename = f"{args.crate_name.replace('-', '_')}.json"
    json_path = target_dir / "doc" / json_filename

    if not json_path.exists():
        print(f"Error: JSON file not found at {json_path}", file=sys.stderr)
        sys.exit(1)

    items = extract_items_from_json(str(json_path))
    print(f"  ✓ Found {len(items)} items")
    print()

    # Step 3: Test each item
    print(f"Step 3: Testing extraction for {len(items)} items...")
    print()

    successes = []
    failures = []

    for i, item in enumerate(items, 1):
        print(f"[{i}/{len(items)}] Testing {item}... ", end="", flush=True)

        success, stage, duration = test_item_extraction(
            item,
            args.crate_name,
            crate_dir,
            workspace_root,
            args.charon,
            args.aeneas,
            args.timeout,
            args.debug
        )

        if success:
            print(f"✓ ({duration:.2f}s)")
            successes.append(item)
        else:
            print(f"✗ (failed at {stage}, {duration:.2f}s)")
            failures.append({"item": item, "stage": stage, "duration": duration})

    # Step 4: Print summary
    print()
    print("=" * 80)
    print(f"RESULTS: {len(successes)}/{len(items)} successes")
    print("=" * 80)
    print()

    print(f"Successes ({len(successes)}):")
    for item in successes:
        print(f"  ✓ {item}")
    print()

    print(f"Failures ({len(failures)}):")
    for failure in failures:
        print(f"  ✗ {failure['item']} (failed at {failure['stage']})")
    print()

    # Save results to JSON if requested
    if args.output:
        results = {
            "total": len(items),
            "successes": len(successes),
            "failures": len(failures),
            "success_list": successes,
            "failure_list": [
                {"item": f["item"], "stage": f["stage"], "duration": f["duration"]}
                for f in failures
            ]
        }

        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"Results saved to {args.output}")


if __name__ == "__main__":
    main()
