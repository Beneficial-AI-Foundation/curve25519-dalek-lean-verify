#!/usr/bin/env python3
"""Benchmark: test how many spec theorems lean-smt can prove directly.

Usage:
  python3 scripts/bench/smt_benchmark.py [output.csv]

For each theorem/lemma in Curve25519Dalek/Specs/, this script:
  1. Extracts all file context up to the theorem's := sign
  2. Replaces the proof body with `by smt`
  3. Runs `lake env lean` on the modified file
  4. Records proved / failed / timeout in a CSV
"""

import csv, re, sys, subprocess, tempfile
from pathlib import Path

ROOT    = Path(__file__).resolve().parent.parent.parent
SPECS   = ROOT / "Curve25519Dalek" / "Specs/Backend/Serial/U64/Constants"
TIMEOUT = 60   # seconds per theorem

# Match top-level theorem/lemma declarations (including optional @[...] attributes)
THM_RE = re.compile(
    r'^(?:@\[(?:[^\]]*)\]\s*\n)*(?:theorem|lemma)\s+(\w+)',
    re.MULTILINE,
)

def find_proof_assign(text: str, decl_end: int) -> int:
    """Return index of ':=' that starts the proof, scanning from decl_end."""
    depth = 0
    i = decl_end
    while i < len(text) - 1:
        if text[i] == '(':  depth += 1
        elif text[i] == ')': depth -= 1
        elif text[i:i+2] == ':=' and depth == 0:
            return i
        i += 1
    return -1

def try_smt(lean_file: Path, decl_start: int, text: str) -> tuple[str, str]:
    """Attempt proof with `by smt`. Returns 'proved', 'failed', or 'timeout'."""
    assign_idx = find_proof_assign(text, decl_start)
    if assign_idx == -1:
        return ("error:no_assign", "")

    # Keep everything up to and including ':=', replace proof with 'by\n  smt'
    stub = text[:assign_idx] + ":= by\n  smt\n"

    with tempfile.NamedTemporaryFile(
        suffix=".lean", dir=lean_file.parent, delete=False, mode='w'
    ) as tmp:
        tmp.write(stub)
        tmp_path = Path(tmp.name)

    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            capture_output=True, text=True, timeout=TIMEOUT, cwd=ROOT,
        )
        # Success = no errors (warnings are OK)
        no_error = r.returncode == 0 and "error:" not in r.stderr
        if no_error:
            return "proved", ""
        else:
            err = (r.stderr + r.stdout).strip()
            return "failed", err
    except subprocess.TimeoutExpired:
        return "timeout", ""
    finally:
        tmp_path.unlink(missing_ok=True)

def main():
    output = sys.argv[1] if len(sys.argv) > 1 else "smt_benchmark.csv"
    lean_files = sorted(SPECS.rglob("*.lean"))
    rows, proved, total = [], 0, 0

    for f in lean_files:
        text = f.read_text()
        for m in THM_RE.finditer(text):
            name = m.group(1)
            status, err = try_smt(f, m.start(), text)
            rows.append({"file": str(f.relative_to(ROOT)), "theorem": name, "status": status})
            proved += status == "proved"
            total  += 1
            marker = "✓" if status == "proved" else "✗"
            print(f"  [{marker}] {f.stem}::{name}  ({status})")
            if err:
                for line in err.splitlines():
                    print(f"      {line}")

    with open(output, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["file", "theorem", "status"])
        w.writeheader()
        w.writerows(rows)

    print(f"\nSMT benchmark: {proved}/{total} proved  →  saved to {output}")

if __name__ == "__main__":
    main()
