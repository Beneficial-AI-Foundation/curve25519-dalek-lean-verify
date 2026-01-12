#!/usr/bin/env python3
"""
Extract the list of commonly verified functions between Lean and Verus
"""

import csv
from pathlib import Path

def normalize_function_name(name):
    """Normalize function name for comparison"""
    return name.strip()

def load_lean_verified(status_file):
    """Load verified functions from status.csv for Lean"""
    lean_verified = set()
    lean_data = {}
    with open(status_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get('verified', '').strip() == 'verified':
                func_name = normalize_function_name(row['function'])
                lean_verified.add(func_name)
                lean_data[func_name] = {
                    'source': row.get('source', ''),
                    'spec_theorem': row.get('spec_theorem', ''),
                    'lines': row.get('lines', '')
                }
    return lean_verified, lean_data

def load_verus_verified(verus_file):
    """Load verified functions from curve25519_functions_normalized.csv for Verus"""
    verus_verified = set()
    verus_data = {}
    with open(verus_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get('has_proof', '').strip() == 'yes':
                func_name = normalize_function_name(row['normalized_path'])
                verus_verified.add(func_name)
                verus_data[func_name] = {
                    'link': row.get('link', ''),
                    'has_spec': row.get('has_spec', '')
                }
    return verus_verified, verus_data

def main():
    status_file = Path('status.csv')
    verus_file = Path('dalek-lite/outputs/curve25519_functions_normalized.csv')

    # Load verified functions
    lean_verified, lean_data = load_lean_verified(status_file)
    verus_verified, verus_data = load_verus_verified(verus_file)

    # Find common verified functions
    both_verified = lean_verified & verus_verified

    print(f"Total commonly verified functions: {len(both_verified)}\n")
    print("List of commonly verified functions:")
    print("=" * 80)

    for func in sorted(both_verified):
        lean_info = lean_data[func]
        verus_info = verus_data[func]
        print(f"\n{func}")
        print(f"  Lean spec: {lean_info['spec_theorem']}")
        print(f"  Lean source: {lean_info['source']} ({lean_info['lines']})")
        print(f"  Verus link: {verus_info['link']}")

if __name__ == '__main__':
    main()
