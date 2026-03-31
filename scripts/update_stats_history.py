#!/usr/bin/env python3
"""Update verification stats history from an enriched functions.json.

Maintains outputs/stats_history.jsonl as an append-only log of verification
progress. Each line is one JSON object with commit, date, and counts.

Modeled on curve25519-dalek (Verus) scripts/update_stats_history.py.

Usage:
    python3 scripts/update_stats_history.py \
        --functions-json functions.json \
        [--fetch-url https://...github.io/.../outputs/stats_history.jsonl] \
        [--fill-missing] [--since 2025-01-01] [--max-commits 5000]
"""

import argparse
import json
import logging
import ssl
import subprocess
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

logging.basicConfig(level=logging.INFO, format="%(message)s")
logger = logging.getLogger(__name__)

HISTORY_FILE = Path("outputs/stats_history.jsonl")


def _stats_from_data(data: dict) -> dict[str, int] | None:
    """Compute verification counts from a parsed functions.json dict."""
    fns = [
        fn for fn in data.get("functions", [])
        if not fn.get("is_hidden") and not fn.get("is_extraction_artifact")
    ]
    if not fns:
        return None
    ext_verified = sum(1 for f in fns if f.get("externally_verified"))
    verified_excl = sum(
        1 for f in fns if f.get("verified") and not f.get("externally_verified")
    )
    specified_excl = sum(
        1 for f in fns
        if f.get("specified") and not f.get("verified") and not f.get("externally_verified")
    )
    return {
        "total": len(fns),
        "verified": verified_excl,
        "externally_verified": ext_verified,
        "specified": specified_excl,
        "extracted": len(fns),
        "fully_verified": sum(1 for f in fns if f.get("fully_verified")),
    }


def compute_stats(functions_json: Path) -> dict[str, int]:
    """Compute verification counts from an enriched functions.json file."""
    with open(functions_json) as f:
        data = json.load(f)
    result = _stats_from_data(data)
    return result if result is not None else {"total": 0, "verified": 0, "externally_verified": 0, "specified": 0, "extracted": 0, "fully_verified": 0}


def read_history(path: Path) -> list[dict]:
    if not path.exists():
        return []
    entries = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
    return entries


def write_history(path: Path, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        for entry in entries:
            f.write(json.dumps(entry, separators=(",", ":")) + "\n")


def fetch_remote_history(url: str) -> list[dict]:
    """Fetch stats_history.jsonl from a URL (e.g. deployed GitHub Pages)."""
    try:
        ctx = ssl.create_default_context()
        req = urllib.request.Request(url, headers={"User-Agent": "update-stats-history/1.0"})
        with urllib.request.urlopen(req, context=ctx, timeout=15) as resp:
            text = resp.read().decode("utf-8")
        entries = []
        for line in text.splitlines():
            line = line.strip()
            if line:
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        logger.info(f"Fetched {len(entries)} entries from {url}")
        return entries
    except Exception as e:
        logger.warning(f"Failed to fetch remote history: {e}")
        return []


def _has_verification_data(entry: dict) -> bool:
    """Return True if the entry has any non-zero verification metrics."""
    return (entry.get("verified", 0) > 0
            or entry.get("specified", 0) > 0
            or entry.get("externally_verified", 0) > 0)


def merge_histories(local: list[dict], remote: list[dict]) -> list[dict]:
    seen: dict[str, dict] = {}
    for entry in local + remote:
        commit = entry.get("commit", "")
        if commit and commit not in seen:
            seen[commit] = entry
    merged = [e for e in seen.values() if _has_verification_data(e)]
    merged.sort(key=lambda x: x.get("date", ""))
    return merged


def get_git_commits(since: str | None, max_commits: int) -> list[dict]:
    """Get commit hashes and dates from git log."""
    cmd = ["git", "log", "--format=%H|%aI", "--reverse"]
    if since:
        cmd.append(f"--since={since}")
    if max_commits:
        cmd.append(f"-n{max_commits}")
    try:
        output = subprocess.check_output(cmd, text=True).strip()
    except subprocess.CalledProcessError:
        return []
    commits = []
    for line in output.splitlines():
        if "|" in line:
            h, d = line.split("|", 1)
            commits.append({"hash": h.strip(), "date": d.strip()})
    return commits


def get_file_at_commit(commit: str, filepath: str) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "show", f"{commit}:{filepath}"],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return None


def stats_from_functions_json_text(text: str) -> dict[str, int] | None:
    """Compute verification counts from a functions.json string."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError:
        return None
    return _stats_from_data(data)


def fill_missing_from_git(
    history: list[dict],
    since: str | None,
    max_commits: int,
) -> list[dict]:
    """Walk git history and fill in missing data points from functions.json."""
    known_commits = {e["commit"] for e in history}
    commits = get_git_commits(since, max_commits)
    added = 0
    for c in commits:
        if c["hash"] in known_commits:
            continue
        text = get_file_at_commit(c["hash"], "functions.json")
        if text is None:
            continue
        stats = stats_from_functions_json_text(text)
        if stats is None:
            continue
        entry = {"commit": c["hash"], "date": c["date"], **stats}
        if not _has_verification_data(entry):
            continue
        history.append(entry)
        added += 1
    if added:
        logger.info(f"Filled {added} missing entries from git history")
        history.sort(key=lambda x: x.get("date", ""))
    return history


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--functions-json", type=Path, default=Path("functions.json"))
    parser.add_argument("--fetch-url", type=str, default=None,
                        help="URL to fetch existing stats_history.jsonl from deployed site")
    parser.add_argument("--fill-missing", action="store_true",
                        help="Walk git history to fill missing entries")
    parser.add_argument("--since", type=str, default=None,
                        help="Only process commits since this date (YYYY-MM-DD)")
    parser.add_argument("--max-commits", type=int, default=5000)
    parser.add_argument("--output", type=Path, default=HISTORY_FILE)
    args = parser.parse_args()

    local_history = read_history(args.output)
    logger.info(f"Local history: {len(local_history)} entries")

    remote_history: list[dict] = []
    if args.fetch_url:
        remote_history = fetch_remote_history(args.fetch_url)

    history = merge_histories(local_history, remote_history)
    logger.info(f"Merged history: {len(history)} entries")

    if args.fill_missing:
        history = fill_missing_from_git(history, args.since, args.max_commits)

    current_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True
    ).strip()
    current_date = datetime.now(timezone.utc).isoformat()

    stats = compute_stats(args.functions_json)
    entry = {"commit": current_commit, "date": current_date, **stats}

    known_commits = {e["commit"] for e in history}
    if current_commit not in known_commits:
        history.append(entry)
        logger.info(f"Appended current: verified={stats['verified']}/{stats['total']}")
    else:
        logger.info("Current commit already in history, skipping append")

    write_history(args.output, history)
    logger.info(f"Wrote {len(history)} entries to {args.output}")


if __name__ == "__main__":
    main()
