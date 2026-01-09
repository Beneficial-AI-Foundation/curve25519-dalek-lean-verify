#!/usr/bin/env python3
"""
Compare verified functions between Lean and Verus
Identifies:
1. Functions verified in Lean but not in Verus
2. Functions verified in Verus but not in Lean
"""

import csv
from pathlib import Path
from collections import defaultdict

def normalize_function_name(name):
    """Normalize function name for comparison"""
    # Remove possible whitespace and special characters
    return name.strip()

def is_constant(func_name):
    """Check if a function is a constant (to be ignored in Lean verification)"""
    return '::constants::' in func_name

def get_module(func_name):
    """Extract module name from function name"""
    parts = func_name.split('::')
    if len(parts) >= 2:
        return '::'.join(parts[:-1])
    return 'unknown'

def load_lean_verified(status_file):
    """Load verified functions from status.csv for Lean, excluding constants"""
    lean_verified = set()
    lean_data = {}  # Store additional information
    with open(status_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get('verified', '').strip() == 'verified':
                func_name = normalize_function_name(row['function'])
                # Skip constants
                if not is_constant(func_name):
                    lean_verified.add(func_name)
                    lean_data[func_name] = {
                        'source': row.get('source', ''),
                        'spec_theorem': row.get('spec_theorem', ''),
                        'status': 'verified'
                    }
    return lean_verified, lean_data

def load_lean_specified(status_file):
    """Load specified functions (specified or verified) from status.csv for Lean, excluding constants"""
    lean_specified = set()
    lean_spec_data = {}  # Store additional information
    with open(status_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            verified_status = row.get('verified', '').strip()
            if verified_status in ['verified', 'specified']:
                func_name = normalize_function_name(row['function'])
                # Skip constants
                if not is_constant(func_name):
                    lean_specified.add(func_name)
                    lean_spec_data[func_name] = {
                        'source': row.get('source', ''),
                        'spec_theorem': row.get('spec_theorem', ''),
                        'status': verified_status
                    }
    return lean_specified, lean_spec_data

def load_verus_verified(verus_file):
    """Load verified functions from curve25519_functions_normalized.csv for Verus"""
    verus_verified = set()
    verus_data = {}  # Store additional information
    with open(verus_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get('has_proof', '').strip() == 'yes':
                func_name = normalize_function_name(row['normalized_path'])
                verus_verified.add(func_name)
                verus_data[func_name] = {
                    'link': row.get('link', ''),
                    'has_spec': row.get('has_spec', ''),
                    'has_proof': 'yes'
                }
    return verus_verified, verus_data

def load_verus_specified(verus_file):
    """Load specified functions (has_spec=yes) from curve25519_functions_normalized.csv for Verus"""
    verus_specified = set()
    verus_spec_data = {}  # Store additional information
    with open(verus_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get('has_spec', '').strip() == 'yes':
                func_name = normalize_function_name(row['normalized_path'])
                verus_specified.add(func_name)
                verus_spec_data[func_name] = {
                    'link': row.get('link', ''),
                    'has_spec': 'yes',
                    'has_proof': row.get('has_proof', '')
                }
    return verus_specified, verus_spec_data

def group_by_module(funcs):
    """Group functions by module"""
    grouped = defaultdict(list)
    for func in funcs:
        module = get_module(func)
        grouped[module].append(func)
    return grouped

def main():
    status_file = Path('status.csv')
    verus_file = Path('dalek-lite/outputs/curve25519_functions_normalized.csv')

    # Load verified functions
    lean_verified, lean_data = load_lean_verified(status_file)
    verus_verified, verus_data = load_verus_verified(verus_file)

    # Load specified functions
    lean_specified, lean_spec_data = load_lean_specified(status_file)
    verus_specified, verus_spec_data = load_verus_specified(verus_file)

    # Find verification differences
    lean_only = lean_verified - verus_verified
    verus_only = verus_verified - lean_verified
    both_verified = lean_verified & verus_verified

    # Find specification differences
    lean_spec_only = lean_specified - verus_specified
    verus_spec_only = verus_specified - lean_specified
    both_specified = lean_specified & verus_specified

    # Group by module
    lean_only_by_module = group_by_module(lean_only)
    verus_only_by_module = group_by_module(verus_only)
    both_verified_by_module = group_by_module(both_verified)
    lean_spec_only_by_module = group_by_module(lean_spec_only)
    verus_spec_only_by_module = group_by_module(verus_spec_only)

    # Output results
    print("=" * 80)
    print("Comparison of Lean and Verus Verified Functions")
    print("=" * 80)
    print(f"\nTotal Lean verified functions: {len(lean_verified)}")
    print(f"Total Verus verified functions: {len(verus_verified)}")
    print(f"Functions verified in both: {len(both_verified)}")
    print(f"\nFunctions verified in Lean but not Verus: {len(lean_only)}")
    print(f"Functions verified in Verus but not Lean: {len(verus_only)}")

    print(f"\nTotal Lean specified functions: {len(lean_specified)}")
    print(f"Total Verus specified functions (has_spec=yes): {len(verus_specified)}")
    print(f"Functions specified in both: {len(both_specified)}")
    print(f"\nFunctions specified in Lean but not Verus: {len(lean_spec_only)}")
    print(f"Functions specified in Verus but not Lean: {len(verus_spec_only)}")

    print("\n" + "=" * 80)
    print("Functions Verified in Lean but Not Verus (by module):")
    print("=" * 80)
    for module in sorted(lean_only_by_module.keys()):
        funcs = sorted(lean_only_by_module[module])
        print(f"\n{module} ({len(funcs)} functions):")
        for func in funcs:
            print(f"  - {func}")

    print("\n" + "=" * 80)
    print("Functions Verified in Verus but Not Lean (by module):")
    print("=" * 80)
    for module in sorted(verus_only_by_module.keys()):
        funcs = sorted(verus_only_by_module[module])
        print(f"\n{module} ({len(funcs)} functions):")
        for func in funcs:
            print(f"  - {func}")

    print("\n" + "=" * 80)
    print("Functions Verified in Both Lean and Verus (by module):")
    print("=" * 80)
    for module in sorted(both_verified_by_module.keys()):
        funcs = sorted(both_verified_by_module[module])
        print(f"\n{module} ({len(funcs)} functions):")
        for func in funcs:
            spec_theorem = lean_data.get(func, {}).get('spec_theorem', '')
            verus_link = verus_data.get(func, {}).get('link', '')
            print(f"  - {func}")
            if spec_theorem:
                print(f"    Lean spec: {spec_theorem}")
            if verus_link:
                print(f"    Verus link: {verus_link}")

    print("\n" + "=" * 80)
    print("Functions Specified in Lean but Not Verus (by module):")
    print("=" * 80)
    for module in sorted(lean_spec_only_by_module.keys()):
        funcs = sorted(lean_spec_only_by_module[module])
        print(f"\n{module} ({len(funcs)} functions):")
        for func in funcs:
            status = lean_spec_data.get(func, {}).get('status', 'unknown')
            print(f"  - {func} [{status}]")

    print("\n" + "=" * 80)
    print("Functions Specified in Verus but Not Lean (by module):")
    print("=" * 80)
    for module in sorted(verus_spec_only_by_module.keys()):
        funcs = sorted(verus_spec_only_by_module[module])
        print(f"\n{module} ({len(funcs)} functions):")
        for func in funcs:
            has_proof = verus_spec_data.get(func, {}).get('has_proof', '')
            proof_status = 'with proof' if has_proof == 'yes' else 'no proof'
            print(f"  - {func} [{proof_status}]")

    
    # Save to Markdown file
    md_file = Path('lean_verus_comparison.md')
    with open(md_file, 'w', encoding='utf-8') as f:
        f.write("# Comparison of Lean and Verus Verified Functions\n\n")
        f.write("## Summary Statistics\n\n")
        f.write(f"- **Total Lean verified functions**: {len(lean_verified)}\n")
        f.write(f"- **Total Verus verified functions**: {len(verus_verified)}\n")
        f.write(f"- **Functions verified in both**: {len(both_verified)}\n")
        f.write(f"- **Functions verified in Lean but not Verus**: {len(lean_only)}\n")
        f.write(f"- **Functions verified in Verus but not Lean**: {len(verus_only)}\n\n")

        f.write(f"- **Total Lean specified functions (specified/verified)**: {len(lean_specified)}\n")
        f.write(f"- **Total Verus specified functions (has_spec=yes)**: {len(verus_specified)}\n")
        f.write(f"- **Functions specified in both**: {len(both_specified)}\n")
        f.write(f"- **Functions specified in Lean but not Verus**: {len(lean_spec_only)}\n")
        f.write(f"- **Functions specified in Verus but not Lean**: {len(verus_spec_only)}\n\n")

        f.write("## Functions Verified in Lean but Not Verus\n\n")
        f.write(f"Total: {len(lean_only)} functions\n\n")
        for module in sorted(lean_only_by_module.keys()):
            funcs = sorted(lean_only_by_module[module])
            f.write(f"### {module}\n\n")
            f.write(f"Total: {len(funcs)} functions:\n\n")
            for func in funcs:
                f.write(f"- `{func}`\n")
            f.write("\n")

        f.write("## Functions Verified in Verus but Not Lean\n\n")
        f.write(f"Total: {len(verus_only)} functions\n\n")
        for module in sorted(verus_only_by_module.keys()):
            funcs = sorted(verus_only_by_module[module])
            f.write(f"### {module}\n\n")
            f.write(f"Total: {len(funcs)} functions:\n\n")
            for func in funcs:
                f.write(f"- `{func}`\n")
            f.write("\n")

        f.write("## Functions Verified in Both Lean and Verus\n\n")
        f.write(f"Total: {len(both_verified)} functions\n\n")
        for module in sorted(both_verified_by_module.keys()):
            funcs = sorted(both_verified_by_module[module])
            f.write(f"### {module}\n\n")
            f.write(f"Total: {len(funcs)} functions:\n\n")
            for func in funcs:
                spec_theorem = lean_data.get(func, {}).get('spec_theorem', '')
                verus_link = verus_data.get(func, {}).get('link', '')
                f.write(f"- `{func}`\n")
                if spec_theorem:
                    f.write(f"  - Lean spec: `{spec_theorem}`\n")
                if verus_link:
                    f.write(f"  - Verus: {verus_link}\n")
            f.write("\n")

        f.write("## Functions Specified in Lean but Not Verus\n\n")
        f.write(f"Total: {len(lean_spec_only)} functions\n\n")
        for module in sorted(lean_spec_only_by_module.keys()):
            funcs = sorted(lean_spec_only_by_module[module])
            f.write(f"### {module}\n\n")
            f.write(f"Total: {len(funcs)} functions:\n\n")
            for func in funcs:
                status = lean_spec_data.get(func, {}).get('status', 'unknown')
                f.write(f"- `{func}` (status: {status})\n")
            f.write("\n")

        f.write("## Functions Specified in Verus but Not Lean\n\n")
        f.write(f"Total: {len(verus_spec_only)} functions\n\n")
        for module in sorted(verus_spec_only_by_module.keys()):
            funcs = sorted(verus_spec_only_by_module[module])
            f.write(f"### {module}\n\n")
            f.write(f"Total: {len(funcs)} functions:\n\n")
            for func in funcs:
                has_proof = verus_spec_data.get(func, {}).get('has_proof', '')
                proof_status = 'with proof' if has_proof == 'yes' else 'no proof'
                f.write(f"- `{func}` ({proof_status})\n")
            f.write("\n")

    print(f"\nResults saved to:")
    print(f"  - {md_file}")

if __name__ == '__main__':
    main()
