#!/usr/bin/env python3
"""
Lean 4 Style Linter for curve25519-dalek-lean-verify.

Checks Lean files against the project style guide (style.md).
Context-free rules are checked via regex/line-scanning.
Context-sensitive rules (A-prefixed) are delegated to an LLM agent when --agent is used.

Usage:
    # Lint specific files:
    python3 scripts/lean_style_linter.py path/to/File.lean ...

    # Lint all Lean files:
    python3 scripts/lean_style_linter.py --all

    # Include LLM-based context-sensitive checks (requires ANTHROPIC_API_KEY):
    python3 scripts/lean_style_linter.py --agent path/to/File.lean

    # Output as JSON (for CI integration):
    python3 scripts/lean_style_linter.py --format json --all

    # GitHub Actions annotation format:
    python3 scripts/lean_style_linter.py --format github --all

Exit codes:
    0  No error-severity violations found.
    1  One or more error-severity violations found.
    2  Usage/configuration error.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Rule catalogue
# ---------------------------------------------------------------------------

RULE_DOCS: dict[str, str] = {
    "R001": "File must begin with a /- ... -/ header block",
    "R002": "Header must contain a Copyright line",
    "R003": "Header must contain the Apache 2.0 license line",
    "R004": "Header must contain an Authors: line",
    "R005": "Lines must be at most 100 characters",
    "R006": "No blank lines between the file header and the first import",
    "R007": "Spec files must have a /-! ... -/ module docstring after imports",
    "R008": "Module docstring must have a # heading and a Source: line",
    "R009": "@[progress] theorem names must end with _spec",
    "R010": "@[progress] attribute must be on its own line at column 0",
    "R011": "@[progress] theorems must use ⦃ ... ⦄ WP syntax",
    "R012": "The result binding in ⦃ ... ⦄ must carry a type annotation",
    "R013": "Every `namespace X` must have a matching `end X`",
    "R014": "Arguments / preconditions must be indented 4 spaces",
    "R015": "Postconditions inside ⦃ ... ⦄ must be indented 6 spaces",
    "R016": "Proof body lines must be indented 2 spaces",
    "R017": "Spec file names must be UpperCamelCase",
    # Context-sensitive (agent) rules
    "A001": "[Agent] Author names must not be AI systems",
    "A002": "[Agent] Spec argument names must match the Rust function parameters",
    "A003": "[Agent] Module docstring must accurately describe the function",
}

# Which rules are errors (vs warnings)
ERROR_RULES: set[str] = {
    "R001", "R002", "R003", "R004", "R005",
    "R009", "R010", "R011", "R013",
    "A001", "A002",
}

# ---------------------------------------------------------------------------
# Violation dataclass
# ---------------------------------------------------------------------------

@dataclass
class Violation:
    rule: str
    line: int           # 1-based; 0 means file-level
    col: Optional[int]  # 1-based or None
    message: str
    file: str = ""

    @property
    def severity(self) -> str:
        return "error" if self.rule in ERROR_RULES else "warning"

    @property
    def is_error(self) -> bool:
        return self.rule in ERROR_RULES

    def as_text(self) -> str:
        loc = self.file
        if self.line:
            loc += f":{self.line}"
            if self.col is not None:
                loc += f":{self.col}"
        sev = self.severity.upper()
        return f"{loc}: [{self.rule}] {sev}: {self.message}"

    def as_github(self) -> str:
        """GitHub Actions workflow command format."""
        sev = self.severity  # 'error' or 'warning'
        parts = [f"::{sev} file={self.file}"]
        if self.line:
            parts.append(f",line={self.line}")
            if self.col is not None:
                parts.append(f",col={self.col}")
        parts.append(f",title={self.rule}::{self.message}")
        return "".join(parts)

    def as_dict(self) -> dict:
        return {
            "rule": self.rule,
            "severity": self.severity,
            "file": self.file,
            "line": self.line,
            "col": self.col,
            "message": self.message,
        }


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def is_spec_file(path: Path) -> bool:
    """True if the file lives under a Specs/ directory."""
    return "Specs" in path.parts


def is_upper_camel_case(name: str) -> bool:
    return bool(re.match(r"^[A-Z][A-Za-z0-9]*$", name))


# ---------------------------------------------------------------------------
# R001–R004: Header block
# ---------------------------------------------------------------------------

_HEADER_OPEN_RE = re.compile(r"^/-$")
_HEADER_CLOSE_RE = re.compile(r"^-/$")
_COPYRIGHT_RE = re.compile(r"^Copyright\b")
_LICENSE_RE = re.compile(
    r"^Released under Apache 2\.0 license as described in the file LICENSE\.$"
)
_AUTHORS_RE = re.compile(r"^Authors:\s*\S")


def check_header(lines: list[str], file_path: str) -> tuple[list[Violation], int]:
    """
    Check header rules R001–R004.
    Returns (violations, header_end_index_0based).
    header_end_index is the line index of the closing -/, or 0 on failure.
    """
    vs: list[Violation] = []

    def V(rule: str, ln: int, msg: str, col: Optional[int] = None) -> None:
        vs.append(Violation(rule, ln, col, msg, file_path))

    if not lines or not _HEADER_OPEN_RE.match(lines[0].rstrip()):
        V("R001", 1, "File must start with a /- ... -/ header block")
        return vs, 0

    # Find closing -/
    header_end = None
    for i in range(1, len(lines)):
        if _HEADER_CLOSE_RE.match(lines[i].rstrip()):
            header_end = i
            break

    if header_end is None:
        V("R001", 1, "Header block /- ... -/ is never closed")
        return vs, 0

    inner = [ln.rstrip() for ln in lines[1:header_end]]

    if not any(_COPYRIGHT_RE.match(l) for l in inner):
        V("R002", 1, 'Header must contain a "Copyright ..." line')
    else:
        # Check "All rights reserved." is present
        if not any("All rights reserved." in l for l in inner):
            V("R002", 1, 'Copyright line should end with "All rights reserved."')

    if not any(_LICENSE_RE.match(l) for l in inner):
        V("R003", 1,
          'Header must contain: "Released under Apache 2.0 license as described in the file LICENSE."')

    if not any(_AUTHORS_RE.match(l) for l in inner):
        V("R004", 1, 'Header must contain an "Authors: ..." line')

    return vs, header_end


# ---------------------------------------------------------------------------
# R006: Imports immediately after header
# ---------------------------------------------------------------------------

def check_imports(
    lines: list[str], header_end: int, file_path: str
) -> tuple[list[Violation], int]:
    """
    Check R006 (no blank lines between header and imports).
    Returns (violations, last_import_line_index_0based).
    """
    vs: list[Violation] = []
    pos = header_end + 1

    # Blank lines before first import
    while pos < len(lines) and not lines[pos].strip():
        vs.append(Violation("R006", pos + 1, None,
                             "No blank lines allowed between header and imports",
                             file_path))
        pos += 1

    last_import = pos - 1
    while pos < len(lines):
        stripped = lines[pos].strip()
        if stripped.startswith("import "):
            last_import = pos
            pos += 1
        elif not stripped:
            break
        else:
            break

    return vs, last_import


# ---------------------------------------------------------------------------
# R007–R008: Module docstring (spec files)
# ---------------------------------------------------------------------------

def check_module_docstring(
    lines: list[str], last_import: int, file_path: str
) -> tuple[list[Violation], int]:
    """
    Check R007/R008 for spec files.
    Returns (violations, docstring_end_index_0based or last_import).
    """
    vs: list[Violation] = []

    def V(rule: str, ln: int, msg: str) -> None:
        vs.append(Violation(rule, ln, None, msg, file_path))

    pos = last_import + 1
    # Skip blank lines
    while pos < len(lines) and not lines[pos].strip():
        pos += 1

    if pos >= len(lines) or not lines[pos].strip().startswith("/-!"):
        V("R007", pos + 1,
          'Spec file should have a /-! ... -/ module docstring after imports')
        return vs, last_import

    doc_start = pos

    # Collect docstring body
    body_lines: list[str] = []
    # The /-! may continue on the same line
    first_content = lines[pos][3:].strip()  # strip "/-!"
    if first_content:
        body_lines.append(first_content)

    doc_end = None
    for i in range(pos + 1, len(lines)):
        stripped = lines[i].strip()
        if stripped == "-/":
            doc_end = i
            break
        body_lines.append(stripped)

    if doc_end is None:
        V("R007", doc_start + 1, "Module docstring /-! ... -/ is never closed")
        return vs, doc_start

    # R008a: must have a # heading
    has_heading = any(l.startswith("#") for l in body_lines)
    if not has_heading:
        V("R008", doc_start + 1,
          'Module docstring should have a # heading '
          '(e.g. "# Spec theorem for `function_name`")')

    # R008b: must have a Source: line
    has_source = any(
        re.search(r"\bSource\b", l, re.IGNORECASE) for l in body_lines
    )
    if not has_source:
        V("R008", doc_start + 1,
          'Module docstring should contain a "Source:" line with the Rust file path')

    return vs, doc_end


# ---------------------------------------------------------------------------
# R005: Line length
# ---------------------------------------------------------------------------

def check_line_lengths(lines: list[str], file_path: str) -> list[Violation]:
    vs = []
    for i, raw in enumerate(lines):
        length = len(raw.rstrip("\n"))
        if length > 100:
            vs.append(Violation("R005", i + 1, 101,
                                f"Line is {length} chars (max 100)", file_path))
    return vs


# ---------------------------------------------------------------------------
# R009–R016: @[progress] theorem checks
# ---------------------------------------------------------------------------

_PROGRESS_ATTR_LINE_RE = re.compile(r"^\s*@\[.*\bprogress\b.*\]")
_THEOREM_START_RE = re.compile(r"^(theorem|def|lemma|abbrev)\s+(\S+)")
_WP_RESULT_TYPED_RE = re.compile(r"⦃\s*\(\s*result\s*:")
_WP_RESULT_UNTYPED_RE = re.compile(r"⦃\s*result\b")


def check_progress_theorems(lines: list[str], file_path: str) -> list[Violation]:
    vs: list[Violation] = []

    def V(rule: str, ln: int, msg: str, col: Optional[int] = None) -> None:
        vs.append(Violation(rule, ln, col, msg, file_path))

    i = 0
    while i < len(lines):
        line = lines[i]

        if not _PROGRESS_ATTR_LINE_RE.match(line):
            i += 1
            continue

        attr_ln = i + 1  # 1-based
        attr_indent = _leading_spaces(line)

        # R010: @[progress] at col 0
        if attr_indent != 0:
            V("R010", attr_ln,
              f"@[progress] attribute should be at column 0 (found {attr_indent} spaces)")

        # R010: @[progress] on its own line (no `theorem` on same line)
        if re.search(r"\btheorem\b", line.split("@[")[0] + line.split("]")[-1]):
            V("R010", attr_ln,
              "@[progress] and theorem keyword must not be on the same line")

        # Find the theorem declaration line (next non-empty line)
        thm_idx = i + 1
        while thm_idx < len(lines) and not lines[thm_idx].strip():
            thm_idx += 1

        if thm_idx >= len(lines):
            i += 1
            continue

        thm_line = lines[thm_idx]
        thm_stripped = thm_line.lstrip()
        thm_match = _THEOREM_START_RE.match(thm_stripped)

        if not thm_match:
            i += 1
            continue

        thm_name_raw = thm_match.group(2)
        # Strip trailing punctuation that may be glued to the name
        thm_name = re.split(r"[\s(:]", thm_name_raw)[0]

        thm_ln = thm_idx + 1  # 1-based

        # R009: name ends with _spec
        if not thm_name.endswith("_spec"):
            V("R009", thm_ln,
              f"@[progress] theorem '{thm_name}' should end with '_spec'")

        # R010: theorem at col 0
        thm_indent = _leading_spaces(thm_line)
        if thm_indent != 0:
            V("R010", thm_ln,
              f"theorem declaration should be at column 0 (found {thm_indent} spaces)")

        # Collect the full signature (up to and including := by)
        sig_lines: list[str] = []
        proof_start: Optional[int] = None
        for j in range(thm_idx, min(thm_idx + 80, len(lines))):
            sig_lines.append(lines[j])
            stripped_j = lines[j].rstrip()
            if re.search(r":=\s*by\s*$", stripped_j) or ":= by" in lines[j]:
                proof_start = j + 1
                break
            if re.search(r":=\s*$", stripped_j):
                proof_start = j + 1
                break

        sig_text = "".join(sig_lines)

        # R011: WP syntax ⦃...⦄
        if "⦃" not in sig_text:
            V("R011", thm_ln,
              f"@[progress] theorem '{thm_name}' should use ⦃ ... ⦄ WP syntax")
        else:
            # R012: result has type annotation
            if not _WP_RESULT_TYPED_RE.search(sig_text):
                if _WP_RESULT_UNTYPED_RE.search(sig_text):
                    vs.append(Violation(
                        "R012", thm_ln, None,
                        f"In '{thm_name}', result binding should carry a type annotation: "
                        "⦃ (result : ResultType) =>",
                        file_path,
                    ))

        # ---- Indentation checks ----
        # Rules (from style.md):
        #   R014: argument/precondition continuation lines → 4 spaces
        #         (includes the function-application line that opens ⦃)
        #   R015: postcondition lines AFTER the ⦃-opening line → 6 spaces
        #   R016: proof body lines → ≥ 2 spaces

        # We track whether we have already seen the line that opens ⦃.
        # The ⦃-opening line itself is an R014 line (4 spaces).
        # Lines that come after it (still inside the signature block) are R015.
        wp_opened = False
        for j, sig_ln in enumerate(sig_lines):
            if j == 0:
                continue  # skip the theorem declaration line itself
            actual_indent = _leading_spaces(sig_ln)
            stripped_sig = sig_ln.strip()

            if not stripped_sig or stripped_sig.startswith("--"):
                continue

            if wp_opened:
                # R015: pure postcondition lines (after ⦃ has been opened)
                # Skip if this line also ends the block with ⦄ inline (e.g. "result = mp ⦄ := by")
                if "⦄" in sig_ln and (":= by" in sig_ln or re.search(r":=\s*$", sig_ln.rstrip())):
                    continue  # combined close+proof-start line; skip indent check
                if actual_indent != 6:
                    vs.append(Violation(
                        "R015", thm_idx + j + 1, None,
                        f"Postcondition lines inside ⦃ ... ⦄ should be indented "
                        f"6 spaces (found {actual_indent})",
                        file_path,
                    ))
            else:
                # R014: argument / precondition / function-application lines → 4 spaces
                if actual_indent != 4:
                    vs.append(Violation(
                        "R014", thm_idx + j + 1, None,
                        f"Argument/precondition lines should be indented 4 spaces "
                        f"(found {actual_indent})",
                        file_path,
                    ))
                # If this line opens the WP block, the next lines are postconditions
                if "⦃" in sig_ln:
                    wp_opened = True

        # R016: proof body at 2 spaces
        if proof_start is not None:
            for j in range(proof_start, min(proof_start + 60, len(lines))):
                pl = lines[j]
                pstripped = pl.strip()
                if not pstripped or pstripped.startswith("--"):
                    continue
                # Stop at the next top-level declaration
                if re.match(
                    r"^(end\s|namespace\s|theorem\s|def\s|lemma\s|@\[|/-|#)",
                    pstripped,
                ):
                    break
                actual_indent = _leading_spaces(pl)
                if actual_indent < 2:
                    vs.append(Violation(
                        "R016", j + 1, None,
                        f"Proof body lines should be indented ≥ 2 spaces "
                        f"(found {actual_indent})",
                        file_path,
                    ))

        i = thm_idx + 1

    return vs


# ---------------------------------------------------------------------------
# R013: Namespace / end matching
# ---------------------------------------------------------------------------

def check_namespace_end(lines: list[str], file_path: str) -> list[Violation]:
    vs: list[Violation] = []
    # Stack entries: (kind, name, 1-based_line) where kind is "namespace" or "section"
    stack: list[tuple[str, str, int]] = []

    for i, raw in enumerate(lines):
        stripped = raw.strip()
        # Skip line comments
        if stripped.startswith("--"):
            continue

        # namespace X
        m = re.match(r"^namespace\s+(\S+)", stripped)
        if m:
            stack.append(("namespace", m.group(1), i + 1))
            continue

        # section X  (section / end also uses same syntax)
        ms = re.match(r"^section\s+(\S+)", stripped)
        if ms:
            stack.append(("section", ms.group(1), i + 1))
            continue

        # end X
        m2 = re.match(r"^end\s+(\S+)", stripped)
        if m2:
            name = m2.group(1)
            # Pop matching entry from the top of the stack
            if stack and stack[-1][1] == name:
                stack.pop()
            else:
                # Search deeper for a match (handles interleaved closes)
                found = next(
                    (k for k, (_, n, _) in enumerate(reversed(stack)) if n == name),
                    None,
                )
                if found is None:
                    vs.append(Violation(
                        "R013", i + 1, None,
                        f"'end {name}' has no matching 'namespace {name}' or 'section {name}'",
                        file_path,
                    ))
            continue

        # bare `end` (closes most-recent block)
        if re.match(r"^end\s*$", stripped) and stack:
            stack.pop()

    # Any unclosed namespace (not section — sections without names are fine)
    for kind, name, ln in stack:
        if kind == "namespace":
            vs.append(Violation(
                "R013", ln, None,
                f"namespace '{name}' opened at line {ln} is never closed with 'end {name}'",
                file_path,
            ))

    return vs


# ---------------------------------------------------------------------------
# R017: File name UpperCamelCase (spec files only)
# ---------------------------------------------------------------------------

def check_filename(path: Path) -> list[Violation]:
    stem = path.stem
    if not is_upper_camel_case(stem):
        return [Violation(
            "R017", 0, None,
            f"Spec file name '{path.name}' should be UpperCamelCase "
            f"(e.g., 'FromBytes.lean')",
            str(path),
        )]
    return []


# ---------------------------------------------------------------------------
# Context-free orchestrator
# ---------------------------------------------------------------------------

_GENERATED_MARKER_RE = re.compile(
    r"AUTOMATICALLY GENERATED|DO NOT EDIT|auto-?generated",
    re.IGNORECASE,
)
_NOLINT_RE = re.compile(r"--\s*lean_style_linter:\s*disable", re.IGNORECASE)


def _is_generated_or_nolint(first_lines: list[str]) -> bool:
    """Return True if the file should be skipped entirely."""
    for line in first_lines[:5]:
        if _GENERATED_MARKER_RE.search(line) or _NOLINT_RE.search(line):
            return True
    return False


def lint_file_context_free(path: Path) -> list[Violation]:
    """Run all context-free rules on a single file."""
    vs: list[Violation] = []
    file_str = str(path)

    try:
        content = path.read_text(encoding="utf-8")
    except Exception as exc:
        return [Violation("R000", 0, None, f"Cannot read file: {exc}", file_str)]

    raw_lines = content.splitlines()

    if _is_generated_or_nolint(raw_lines):
        return []  # skip auto-generated files silently

    spec = is_spec_file(path)

    # R005 — line length
    vs.extend(check_line_lengths(raw_lines, file_str))

    # R001–R004 — header
    header_vs, header_end = check_header(raw_lines, file_str)
    vs.extend(header_vs)

    # R006 + import boundary
    import_vs, last_import = check_imports(raw_lines, header_end, file_str)
    vs.extend(import_vs)

    # R007–R008 — module docstring (spec files only)
    if spec:
        doc_vs, _ = check_module_docstring(raw_lines, last_import, file_str)
        vs.extend(doc_vs)

    # R009–R016 — @[progress] theorem structure
    vs.extend(check_progress_theorems(raw_lines, file_str))

    # R013 — namespace / end matching
    vs.extend(check_namespace_end(raw_lines, file_str))

    # R017 — file name (spec files only)
    if spec:
        vs.extend(check_filename(path))

    return vs


# ---------------------------------------------------------------------------
# Agent-based context-sensitive checks (A001–A003)
# ---------------------------------------------------------------------------

_AI_NAME_PATTERNS = [
    r"\bClaude\b", r"\bChatGPT\b", r"\bGPT-?\d", r"\bCopilot\b",
    r"\bGemini\b", r"\bBard\b", r"\bLlama\b", r"\bMistral\b",
    r"\bCodex\b", r"\bDeepSeek\b", r"\bGrok\b",
]
_AI_NAMES_RE = re.compile("|".join(_AI_NAME_PATTERNS), re.IGNORECASE)


def _check_authors_heuristic(lines: list[str], file_path: str) -> list[Violation]:
    """
    Heuristic A001 check: flag author lines that contain known AI system names.
    This is fast enough to run without calling the API.
    """
    vs = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("Authors:"):
            m = _AI_NAMES_RE.search(stripped)
            if m:
                vs.append(Violation(
                    "A001", i + 1, None,
                    f"Authors line contains a name that looks like an AI system: "
                    f"'{m.group(0)}'. AIs cannot be listed as authors.",
                    file_path,
                ))
    return vs


def lint_file_agent(path: Path) -> list[Violation]:
    """
    Run context-sensitive checks via the Anthropic API.
    Requires the ANTHROPIC_API_KEY environment variable.
    """
    vs: list[Violation] = []
    file_str = str(path)

    try:
        import anthropic  # type: ignore
    except ImportError:
        vs.append(Violation(
            "A000", 0, None,
            "anthropic Python package not installed; cannot run agent checks. "
            "Install with: pip install anthropic",
            file_str,
        ))
        return vs

    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        vs.append(Violation(
            "A000", 0, None,
            "ANTHROPIC_API_KEY environment variable is not set; skipping agent checks.",
            file_str,
        ))
        return vs

    try:
        content = path.read_text(encoding="utf-8")
    except Exception as exc:
        return [Violation("A000", 0, None, f"Cannot read file: {exc}", file_str)]

    # Quick heuristic (no API call needed)
    vs.extend(_check_authors_heuristic(content.splitlines(), file_str))

    # ---- Build the prompt for the LLM ----
    prompt = f"""\
You are a Lean 4 code style checker. Inspect the following Lean file for violations
of these context-sensitive style rules:

A001: Author names must not be AI systems.
      The Authors: header line must list only human names.
      AIs (Claude, ChatGPT, Copilot, Gemini, etc.) cannot be listed as authors.

A002: Spec theorem argument names must match the corresponding Rust function parameters.
      Each @[progress] theorem encodes a spec for a Rust function.
      Verify that the argument names in the Lean theorem are identical to the parameter
      names used in the original Rust function (if you can infer it from the docstring
      or function name).

A003: The module docstring (/-! ... -/) must accurately describe the function it covers.
      It should state what the function computes, mention the Source path, and not
      contradict what the theorem actually asserts.

Return a JSON array of violation objects (empty array if no violations). Each object must have:
  - "rule": one of "A001", "A002", "A003"
  - "line": the 1-based line number (0 if file-level)
  - "message": a concise human-readable description of the problem

Do not include any text outside the JSON array.

--- BEGIN FILE: {path.name} ---
{content[:8000]}
--- END FILE ---
"""

    try:
        client = anthropic.Anthropic(api_key=api_key)
    except Exception as exc:
        vs.append(Violation(
            "A000", 0, None,
            f"Could not create Anthropic client: {exc}",
            file_str,
        ))
        return vs

    try:
        response = client.messages.create(
            model="claude-haiku-4-5-20251001",
            max_tokens=1024,
            messages=[{"role": "user", "content": prompt}],
        )
        block = response.content[0]
        raw = (block.text if hasattr(block, "text") else "").strip()  # type: ignore[union-attr]
        # Extract JSON even if the model wrapped it in markdown
        json_match = re.search(r"\[.*\]", raw, re.DOTALL)
        if json_match:
            findings = json.loads(json_match.group(0))
            for f in findings:
                vs.append(Violation(
                    f.get("rule", "A000"),
                    int(f.get("line", 0)),
                    None,
                    f.get("message", "(no message)"),
                    file_str,
                ))
    except Exception as exc:
        vs.append(Violation(
            "A000", 0, None,
            f"Agent check failed: {exc}",
            file_str,
        ))

    return vs


# ---------------------------------------------------------------------------
# File discovery
# ---------------------------------------------------------------------------

_DEFAULT_EXCLUDE_DIRS: set[str] = {".lake", "build", "_build", "node_modules"}


def find_lean_files(root: Path, exclude_dirs: set[str] | None = None) -> list[Path]:
    """Return all .lean files under root, excluding dependency/build directories."""
    excluded = exclude_dirs if exclude_dirs is not None else _DEFAULT_EXCLUDE_DIRS
    results = []
    for p in root.rglob("*.lean"):
        # Skip if any path component is in the excluded set
        if any(part in excluded for part in p.parts):
            continue
        results.append(p)
    return sorted(results)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def print_text(violations: list[Violation], show_warnings: bool = True) -> None:
    for v in violations:
        if not show_warnings and not v.is_error:
            continue
        print(v.as_text())


def print_github(violations: list[Violation]) -> None:
    for v in violations:
        print(v.as_github())


def print_json(violations: list[Violation]) -> None:
    print(json.dumps([v.as_dict() for v in violations], indent=2, ensure_ascii=False))


def print_summary(violations: list[Violation], n_files: int) -> None:
    errors = sum(1 for v in violations if v.is_error)
    warnings = sum(1 for v in violations if not v.is_error)
    print(
        f"\n── Linted {n_files} file(s): "
        f"{errors} error(s), {warnings} warning(s) ──"
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument(
        "files", nargs="*", metavar="FILE",
        help="Lean files to lint (default: none; use --all for all files)",
    )
    p.add_argument(
        "--all", dest="lint_all", action="store_true",
        help="Lint every .lean file in the project",
    )
    p.add_argument(
        "--agent", action="store_true",
        help="Also run context-sensitive LLM-based checks (requires ANTHROPIC_API_KEY)",
    )
    p.add_argument(
        "--spec-only", action="store_true",
        help="Only apply rules relevant to spec theorem files",
    )
    p.add_argument(
        "--errors-only", action="store_true",
        help="Suppress warnings; only report errors",
    )
    p.add_argument(
        "--format", choices=["text", "json", "github"], default="text",
        help="Output format (default: text)",
    )
    p.add_argument(
        "--rules", metavar="R001,R002,...",
        help="Comma-separated list of rules to enable (default: all)",
    )
    p.add_argument(
        "--ignore", metavar="R001,R002,...",
        help="Comma-separated list of rules to suppress",
    )
    p.add_argument(
        "--list-rules", action="store_true",
        help="Print all rule codes and descriptions, then exit",
    )
    p.add_argument(
        "--root", metavar="DIR", default=".",
        help="Project root for --all (default: current directory)",
    )
    p.add_argument(
        "--exclude", metavar="DIR,...",
        help=(
            "Comma-separated directory names to exclude when using --all "
            f"(default: {','.join(sorted(_DEFAULT_EXCLUDE_DIRS))})"
        ),
    )
    return p


def main(argv: Optional[list[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.list_rules:
        for code, desc in sorted(RULE_DOCS.items()):
            sev = "ERROR  " if code in ERROR_RULES else "warning"
            print(f"  {code}  [{sev}]  {desc}")
        return 0

    # Determine file list
    exclude_dirs: set[str] | None = None
    if args.exclude:
        exclude_dirs = set(args.exclude.split(","))

    paths: list[Path] = []
    if args.lint_all:
        root = Path(args.root)
        paths = find_lean_files(root, exclude_dirs)
    elif args.files:
        paths = [Path(f) for f in args.files]
    else:
        parser.print_help()
        return 2

    if not paths:
        print("No .lean files found.", file=sys.stderr)
        return 0

    # Rule filter
    enabled: Optional[set[str]] = None
    if args.rules:
        enabled = set(args.rules.split(","))
    ignored: set[str] = set()
    if args.ignore:
        ignored = set(args.ignore.split(","))

    all_violations: list[Violation] = []

    for path in paths:
        # Context-free
        vs = lint_file_context_free(path)

        # Context-sensitive (agent)
        if args.agent:
            vs.extend(lint_file_agent(path))

        # Apply rule filters
        if enabled is not None:
            vs = [v for v in vs if v.rule in enabled]
        if ignored:
            vs = [v for v in vs if v.rule not in ignored]

        if args.spec_only:
            spec_rules = {
                "R007", "R008", "R009", "R010", "R011",
                "R012", "R013", "R014", "R015", "R016", "R017",
                "A002", "A003",
            }
            vs = [v for v in vs if v.rule in spec_rules]

        all_violations.extend(vs)

    # Output
    fmt = args.format
    if fmt == "json":
        print_json(all_violations)
    elif fmt == "github":
        print_github(all_violations)
    else:
        print_text(all_violations, show_warnings=not args.errors_only)
        if not args.errors_only:
            print_summary(all_violations, len(paths))

    has_errors = any(v.is_error for v in all_violations)
    return 1 if has_errors else 0


if __name__ == "__main__":
    sys.exit(main())
