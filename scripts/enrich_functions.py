#!/usr/bin/env python3
"""Enrich a basic functions.json (from probe-aeneas listfuns) with verification
data from a probe-lean extract atoms JSON.

Usage:
    python3 scripts/enrich_functions.py \
        --functions functions.json \
        --atoms lean_atoms.json \
        --config scripts/functions_config.json \
        --output functions.json

The atoms JSON is the direct output of `probe-lean extract`.
The config JSON mirrors the curated lists from Utils/Config.lean (hidden,
ignored, artifact suffixes, excluded prefixes) so the CI pipeline produces
identical categorisation to `lake exe listfuns`.
"""

import argparse
import json
from pathlib import Path

PROBE_PREFIX = "probe:"


def load_json(path: Path) -> dict:
    with open(path) as f:
        return json.load(f)


def strip_prefix(s: str) -> str:
    return s[len(PROBE_PREFIX):] if s.startswith(PROBE_PREFIX) else s


def compute_fully_verified(
    lean_name: str,
    atoms: dict[str, dict],
    cache: dict[str, bool],
) -> bool:
    """Walk dependencies transitively; True only if every dep is verified."""
    if lean_name in cache:
        return cache[lean_name]

    cache[lean_name] = False  # cycle guard

    key = f"{PROBE_PREFIX}{lean_name}"
    atom = atoms.get(key)
    if atom is None:
        cache[lean_name] = False
        return False

    primary_key = atom.get("primary-spec")
    if not primary_key:
        spec_key = f"{key}_spec"
        if spec_key in atoms:
            primary_key = spec_key

    if primary_key:
        spec_atom = atoms.get(primary_key, {})
        if spec_atom.get("verification-status") != "verified":
            cache[lean_name] = False
            return False

    for dep_key in atom.get("dependencies", []):
        dep_name = strip_prefix(dep_key)
        dep_atom = atoms.get(dep_key)
        if dep_atom is None:
            continue
        if dep_atom.get("code-path", "").endswith("Funs.lean"):
            if not compute_fully_verified(dep_name, atoms, cache):
                cache[lean_name] = False
                return False

    cache[lean_name] = True
    return True


def apply_config_flags(
    fn: dict,
    hidden_set: set[str],
    ignored_set: set[str],
    artifact_suffixes: list[str],
    excluded_prefixes: list[str],
) -> None:
    """Apply the curated categorisation from functions_config.json.

    These override whatever gen_functions set, matching the old lake exe
    listfuns behaviour exactly.
    """
    name = fn["lean_name"]

    if any(name.startswith(p) for p in excluded_prefixes):
        fn["is_hidden"] = True
        return

    fn["is_extraction_artifact"] = any(
        name.endswith(s) for s in artifact_suffixes
    )

    fn["is_hidden"] = name in hidden_set
    fn["is_ignored"] = name in ignored_set


def enrich(
    functions: dict,
    atoms: dict[str, dict],
    config: dict,
) -> dict:
    hidden_set = set(config.get("hidden_functions", []))
    ignored_set = set(config.get("ignored_functions", []))
    artifact_suffixes = config.get("extraction_artifact_suffixes", [])
    excluded_prefixes = config.get("excluded_namespace_prefixes", [])

    fv_cache: dict[str, bool] = {}

    for fn in functions.get("functions", []):
        lean_name = fn["lean_name"]
        key = f"{PROBE_PREFIX}{lean_name}"
        atom = atoms.get(key)

        if atom is None:
            fn.setdefault("specified", False)
            fn.setdefault("verified", False)
            fn.setdefault("externally_verified", False)
            fn.setdefault("fully_verified", False)
            fn.setdefault("dependencies", [])
            fn.setdefault("spec_file", None)
            fn.setdefault("spec_docstring", None)
            fn.setdefault("spec_statement", None)
            fn.setdefault("is_relevant", False)
            apply_config_flags(
                fn, hidden_set, ignored_set, artifact_suffixes,
                excluded_prefixes,
            )
            continue

        primary_key = atom.get("primary-spec")
        if not primary_key:
            spec_key = f"{key}_spec"
            if spec_key in atoms:
                primary_key = spec_key

        primary_atom = atoms.get(primary_key, {}) if primary_key else {}

        fn["specified"] = primary_key is not None
        fn["verified"] = primary_atom.get("verification-status") == "verified"

        spec_attrs = primary_atom.get("attributes", [])
        fn["externally_verified"] = "externally_verified" in spec_attrs

        fn["spec_file"] = primary_atom.get("code-path") if primary_key else None
        fn["is_relevant"] = atom.get("is-relevant", False)

        fn["dependencies"] = [
            strip_prefix(d)
            for d in atom.get("dependencies", [])
        ]

        fn.setdefault("spec_docstring", None)
        fn.setdefault("spec_statement", None)

        fn["fully_verified"] = compute_fully_verified(lean_name, atoms, fv_cache)

        apply_config_flags(
            fn, hidden_set, ignored_set, artifact_suffixes,
            excluded_prefixes,
        )

    return functions


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--functions", required=True, type=Path,
                        help="Basic functions.json from probe-aeneas listfuns")
    parser.add_argument("--atoms", required=True, type=Path,
                        help="Atoms JSON from probe-lean extract")
    parser.add_argument("--config", required=True, type=Path,
                        help="Curated config JSON (from Utils/Config.lean)")
    parser.add_argument("--output", required=True, type=Path,
                        help="Output enriched functions.json path")
    args = parser.parse_args()

    functions = load_json(args.functions)
    atoms_envelope = load_json(args.atoms)
    atoms = atoms_envelope.get("data", {})
    config = load_json(args.config)

    enriched = enrich(functions, atoms, config)

    with open(args.output, "w") as f:
        json.dump(enriched, f, indent=2, ensure_ascii=False)
        f.write("\n")

    total = len(enriched.get("functions", []))
    visible = [fn for fn in enriched["functions"]
               if not fn.get("is_hidden")
               and not fn.get("is_extraction_artifact")
               and not fn.get("is_ignored")]
    verified = sum(1 for fn in visible if fn.get("verified"))
    specified = sum(1 for fn in visible if fn.get("specified"))
    ext_v = sum(1 for fn in visible if fn.get("externally_verified"))
    fully_v = sum(1 for fn in visible if fn.get("fully_verified"))

    print(f"Enriched {total} functions ({len(visible)} visible)")
    print(f"  verified={verified}  specified={specified}  "
          f"externally_verified={ext_v}  fully_verified={fully_v}")


if __name__ == "__main__":
    main()
