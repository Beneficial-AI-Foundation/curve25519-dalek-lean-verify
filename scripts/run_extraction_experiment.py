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
import signal
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from extract_items import extract_items_from_json


def run_command(cmd, timeout, cwd, debug):
    """
    Run a command with timeout, properly killing child processes on timeout.

    Returns:
        (success: bool, duration: float, exit_code: int|None, timed_out: bool, stdout: str, stderr: str)
        exit_code is None if timed out
    """
    start = time.time()
    try:
        # Use Popen with start_new_session=True to properly handle child processes
        p = subprocess.Popen(
            cmd,
            shell=True,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True
        )

        # Wait for completion with timeout
        stdout, stderr = p.communicate(timeout=timeout)
        duration = time.time() - start

        if debug and (stdout or stderr):
            print("\n--- STDOUT ---")
            print(stdout)
            print("--- STDERR ---")
            print(stderr)
            print("--- END ---\n")

        return p.returncode == 0, duration, p.returncode, False, stdout, stderr
    except subprocess.TimeoutExpired:
        duration = time.time() - start

        # Kill the whole process group to ensure all children are terminated
        if debug:
            print("\n[Command timed out]")
            print("Terminating the whole process group...", file=sys.stderr)

        try:
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
        except ProcessLookupError:
            # Process already died
            pass

        # Try to get any partial output
        try:
            stdout, stderr = p.communicate(timeout=1)
        except:
            stdout, stderr = "", ""

        if debug:
            if stdout or stderr:
                print("--- STDOUT (before timeout) ---")
                print(stdout)
                print("--- STDERR (before timeout) ---")
                print(stderr)
                print("--- END ---\n")
            else:
                print()

        return False, duration, None, True, stdout, stderr


def remove_llbc_files(cwd):
    """Remove all .llbc files in the directory."""
    llbc_files = Path(cwd).glob("*.llbc")
    for f in llbc_files:
        f.unlink()


def test_item_extraction(item_path, crate_name, cwd, workspace_root, charon_path, aeneas_path, timeout, debug):
    """
    Test if an item can be extracted with Charon and Aeneas.

    Returns:
        (success: bool, result_info: dict, logs: dict)
        result_info contains: stage, charon_duration, aeneas_duration, exit_code, timed_out
        logs contains: charon_stdout, charon_stderr, aeneas_stdout, aeneas_stderr
    """
    # Remove old LLBC files (in workspace root where charon generates them)
    remove_llbc_files(workspace_root)

    # Run cargo clean to clear build artifacts and lock files
    clean_cmd = "cargo clean"
    run_command(clean_cmd, 30, cwd, False)  # Don't print output unless debug

    # Run Charon (from crate directory)
    charon_cmd = f"RUST_BACKTRACE=1 {charon_path} cargo --preset=aeneas --start-from '{item_path}' --error-on-warnings"
    charon_success, charon_duration, charon_exit_code, charon_timed_out, charon_stdout, charon_stderr = run_command(charon_cmd, timeout, cwd, debug)

    logs = {
        "charon_stdout": charon_stdout,
        "charon_stderr": charon_stderr,
        "aeneas_stdout": None,
        "aeneas_stderr": None
    }

    if not charon_success:
        return False, {
            "stage": "charon",
            "charon_duration": charon_duration,
            "aeneas_duration": None,
            "exit_code": charon_exit_code,
            "timed_out": charon_timed_out
        }, logs

    # Run Aeneas (from workspace root where .llbc file is)
    llbc_file = f"{crate_name.replace('-', '_')}.llbc"
    aeneas_cmd = f"{aeneas_path} -backend lean -split-files {llbc_file}"
    aeneas_success, aeneas_duration, aeneas_exit_code, aeneas_timed_out, aeneas_stdout, aeneas_stderr = run_command(aeneas_cmd, timeout, workspace_root, debug)

    logs["aeneas_stdout"] = aeneas_stdout
    logs["aeneas_stderr"] = aeneas_stderr

    if not aeneas_success:
        return False, {
            "stage": "aeneas",
            "charon_duration": charon_duration,
            "aeneas_duration": aeneas_duration,
            "exit_code": aeneas_exit_code,
            "timed_out": aeneas_timed_out
        }, logs

    return True, {
        "stage": "success",
        "charon_duration": charon_duration,
        "aeneas_duration": aeneas_duration,
        "exit_code": 0,
        "timed_out": False
    }, logs


def main():
    parser = argparse.ArgumentParser(
        description="Run extraction experiments with Charon and Aeneas"
    )
    parser.add_argument(
        "crate_dir",
        help="Directory containing the Rust crate to test"
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
        default=20,
        help="Timeout in seconds for charon and aeneas commands (default: 20)"
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
    rustdoc_cmd = "cargo +nightly rustdoc --all-features -- -Z unstable-options --output-format json --document-private-items"
    success, duration, _, _, _, _ = run_command(rustdoc_cmd, 60, crate_dir, args.debug)

    if not success:
        print("Error: Failed to generate rustdoc JSON", file=sys.stderr)
        sys.exit(1)

    print(f"  ✓ Generated in {duration:.2f}s")
    print()

    # Step 2: Extract items
    print("Step 2: Extracting items from rustdoc JSON...")

    doc_dir = target_dir / "doc"
    if not doc_dir.exists():
        print(f"Error: Doc directory not found at {doc_dir}", file=sys.stderr)
        sys.exit(1)

    # Find all JSON files in doc directory
    json_files = list(doc_dir.glob("*.json"))

    if len(json_files) == 0:
        print(f"Error: No JSON files found in {doc_dir}", file=sys.stderr)
        sys.exit(1)
    elif len(json_files) > 1:
        print(f"Error: Multiple JSON files found in {doc_dir}:", file=sys.stderr)
        for jf in json_files:
            print(f"  - {jf.name}", file=sys.stderr)
        print("Likely this script needs tweaking so you can choose the right one", file=sys.stderr)
        sys.exit(1)

    json_path = json_files[0]
    print(f"  Using JSON file: {json_path.name}")

    # Derive crate name from JSON filename (remove .json extension)
    crate_name = json_path.stem
    print(f"  Crate name: {crate_name}")

    items = extract_items_from_json(str(json_path))
    print(f"  ✓ Found {len(items)} items")
    print()

    # Step 3: Test each item
    print(f"Step 3: Testing extraction for {len(items)} items...")
    print()

    successes = []
    failures = []
    all_logs = []  # Collect all logs for saving at the end

    for i, item in enumerate(items, 1):
        print(f"[{i}/{len(items)}] Testing {item}... ", end="", flush=True)

        success, result_info, logs = test_item_extraction(
            item,
            crate_name,
            crate_dir,
            workspace_root,
            args.charon,
            args.aeneas,
            args.timeout,
            args.debug
        )

        # Store logs for this item
        all_logs.append({
            "item": item,
            "success": success,
            "result_info": result_info,
            "logs": logs
        })

        if success:
            charon_time = result_info["charon_duration"]
            aeneas_time = result_info["aeneas_duration"]
            total_time = charon_time + aeneas_time
            print(f"✓ (charon: {charon_time:.2f}s, aeneas: {aeneas_time:.2f}s, total: {total_time:.2f}s)")
            successes.append(item)
        else:
            stage = result_info["stage"]
            charon_time = result_info["charon_duration"]
            aeneas_time = result_info["aeneas_duration"]
            exit_code = result_info["exit_code"]
            timed_out = result_info["timed_out"]

            error_info = f"failed at {stage}"
            if timed_out:
                error_info += " (timeout)"
            elif exit_code is not None:
                error_info += f" (exit code {exit_code})"

            times = f"charon: {charon_time:.2f}s"
            if aeneas_time is not None:
                times += f", aeneas: {aeneas_time:.2f}s"

            print(f"✗ ({error_info}, {times})")
            failures.append({
                "item": item,
                "stage": stage,
                "charon_duration": charon_time,
                "aeneas_duration": aeneas_time,
                "exit_code": exit_code,
                "timed_out": timed_out
            })

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
        error_info = f"failed at {failure['stage']}"
        if failure['timed_out']:
            error_info += " (timeout)"
        elif failure['exit_code'] is not None:
            error_info += f" (exit code {failure['exit_code']})"
        print(f"  ✗ {failure['item']} ({error_info})")
    print()

    # Save results to JSON if requested
    if args.output:
        results = {
            "total": len(items),
            "successes": len(successes),
            "failures": len(failures),
            "success_list": successes,
            "failure_list": failures
        }

        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"Results saved to {args.output}")

    # Save detailed logs with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_filename = f"extraction_logs_{crate_name}_{timestamp}.json"
    log_path = workspace_root / log_filename

    with open(log_path, 'w') as f:
        json.dump(all_logs, f, indent=2)

    print(f"Detailed logs saved to {log_path}")


if __name__ == "__main__":
    main()
