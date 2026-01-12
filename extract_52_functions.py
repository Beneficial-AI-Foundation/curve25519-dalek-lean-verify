#!/usr/bin/env python3
"""
Extract the 52 functions that are specified in both Lean and Verus
"""

import csv
import json
from pathlib import Path

def load_verus_data():
    """Load Verus specification data from dalek-lite/outputs/curve25519_functions_normalized.csv"""
    verus_specs = {}
    verus_path = Path("dalek-lite/outputs/curve25519_functions_normalized.csv")

    if not verus_path.exists():
        print(f"Warning: {verus_path} not found!")
        return {}

    with open(verus_path, "r", encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            # A function has spec if has_spec == 'yes'
            if row.get('has_spec', '').strip() == 'yes':
                func_name = row['normalized_path'].strip()
                verus_specs[func_name] = {
                    'link': row.get('link', ''),
                    'has_proof': row.get('has_proof', '').strip() == 'yes',
                    'module': row.get('module', '')
                }

    return verus_specs

def load_lean_data():
    """Load Lean specification data from status.csv"""
    lean_specs = {}
    with open("status.csv", "r", encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            func_name = row['function'].strip()
            verified_status = row['verified'].strip()
            spec_theorem = row['spec_theorem'].strip()

            # Consider a function specified in Lean if it has a spec_theorem and verified status
            # (verified or specified)
            if spec_theorem and verified_status in ['verified', 'specified']:
                lean_specs[func_name] = {
                    'status': verified_status,
                    'spec_file': spec_theorem,
                    'lean_name': row['lean_name'],
                    'source': row['source'],
                    'lines': row['lines']
                }

    return lean_specs

def main():
    lean_specs = load_lean_data()
    verus_specs = load_verus_data()

    print(f"Total Lean specified functions: {len(lean_specs)}")
    print(f"Total Verus specified functions: {len(verus_specs)}")
    print()

    # Find functions specified in both
    both_specs = []
    for func_name in lean_specs:
        if func_name in verus_specs:
            both_specs.append({
                'function': func_name,
                'lean_status': lean_specs[func_name]['status'],
                'lean_spec_file': lean_specs[func_name]['spec_file'],
                'lean_source': lean_specs[func_name]['source'],
                'lean_lines': lean_specs[func_name]['lines'],
                'verus_link': verus_specs[func_name]['link'],
                'verus_has_proof': verus_specs[func_name]['has_proof'],
                'verus_module': verus_specs[func_name]['module']
            })

    # Sort by function name
    both_specs.sort(key=lambda x: x['function'])

    print(f"Total functions specified in both Lean and Verus: {len(both_specs)}\n")

    # Group by verification status
    verified = [f for f in both_specs if f['lean_status'] == 'verified']
    specified = [f for f in both_specs if f['lean_status'] == 'specified']

    print(f"Verified in Lean: {len(verified)}")
    print(f"  - Of which Verus has proof: {sum(1 for f in verified if f['verus_has_proof'])}")
    print(f"Specified in Lean (not verified): {len(specified)}")
    print(f"  - Of which Verus has proof: {sum(1 for f in specified if f['verus_has_proof'])}")
    print()

    # Print all functions
    print("=" * 80)
    print("All 52 functions specified in both Lean and Verus:")
    print("=" * 80)
    for i, func in enumerate(both_specs, 1):
        verus_status = "verified" if func['verus_has_proof'] else "specified"
        print(f"{i}. {func['function']}")
        print(f"   Lean: {func['lean_status']:12s} | Verus: {verus_status:12s}")
        print(f"   Lean spec: {func['lean_spec_file']}")
        print(f"   Verus: {func['verus_link']}")
        print()

    # Save to file for further processing
    with open("functions_in_both.json", "w") as f:
        json.dump(both_specs, f, indent=2)

    print(f"\nSaved to functions_in_both.json")

    return both_specs

if __name__ == "__main__":
    main()
