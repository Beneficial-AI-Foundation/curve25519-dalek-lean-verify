#!/usr/bin/env python3
"""
Normalize function paths in status.csv and curve25519_functions.csv
to make them easier to compare.

This script:
1. Adds a 'normalized_path' column to both files
2. For curve25519_functions.csv: infers full paths for functions without type prefixes
3. Adds a 'normalization_failed' column to curve25519_functions.csv to mark rows
   where normalization failed and fell back to module-only format
4. For status.csv: uses the existing full path format
"""

import csv
import re
from pathlib import Path
from typing import Dict, Optional, Tuple

def extract_line_number_from_link(link: str) -> Optional[int]:
    """Extract line number from GitHub link like #L667"""
    match = re.search(r'#L(\d+)', link)
    return int(match.group(1)) if match else None

def find_impl_block_for_function(
    file_path: Path,
    function_name: str,
    line_hint: Optional[int] = None
) -> Optional[str]:
    """
    Find which impl block a function belongs to by parsing the Rust source.
    Returns the type name (e.g., 'RistrettoPoint') or None if not found.
    Prefers outermost impl blocks over nested ones.
    """
    if not file_path.exists():
        return None

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception:
        return None

    # Find the function definition
    fn_pattern = re.compile(r'\b(?:pub\s+)?(?:pub\([^)]+\)\s+)?(?:const\s+)?fn\s+' + re.escape(function_name) + r'\s*[<\(]')

    # If we have a line hint, search around that line
    search_start = max(0, (line_hint or 0) - 100) if line_hint else 0
    search_end = min(len(lines), (line_hint or 0) + 50) if line_hint else len(lines)

    # Look for the function in the specified range
    fn_line = None
    for i in range(search_start, search_end):
        if fn_pattern.search(lines[i]):
            fn_line = i
            break

    if fn_line is None:
        return None

    # Calculate indentation of the function (to find matching impl block)
    fn_indent = len(lines[fn_line]) - len(lines[fn_line].lstrip())

    # Look backwards for impl blocks, preferring those with less indentation (outermost)
    candidates = []
    brace_depth = 0
    in_function = False

    for j in range(fn_line, max(-1, fn_line - 500), -1):
        line = lines[j]
        stripped = line.lstrip()
        line_indent = len(line) - len(stripped)

        # Track brace depth to detect when we leave nested blocks
        brace_depth += stripped.count('}') - stripped.count('{')

        # Match: impl TypeName { or impl Trait for TypeName {
        impl_match = re.search(r'impl\s+([A-Za-z0-9_]+)(?:\s+for\s+([A-Za-z0-9_<>]+))?\s*\{', stripped)
        if impl_match:
            impl_indent = line_indent
            # If it's a trait impl, use the type name (second group)
            # Otherwise use the first group
            type_name = impl_match.group(2) or impl_match.group(1)
            # Clean up generic parameters if present
            if '<' in type_name:
                type_name = type_name.split('<')[0]

            # Only consider impl blocks that are at the same or less indentation as the function
            # This ensures we get the outermost impl block that contains the function
            if impl_indent <= fn_indent:
                candidates.append((impl_indent, type_name, j))

    # Return the candidate with the least indentation (most outer)
    if candidates:
        candidates.sort(key=lambda x: (x[0], -x[2]))  # Sort by indent (asc), then by line number (desc)
        return candidates[0][1]

    return None

def normalize_curve25519_function_path(
    func_name: str,
    module: str,
    link: str,
    functions_to_track: Optional[Dict[str, str]] = None
) -> Tuple[str, bool]:
    """
    Normalize a function path from curve25519_functions.csv to full Rust path format.
    
    Returns:
        Tuple of (normalized_path, is_fallback) where is_fallback is True if
        the normalization failed and fell back to module-only format.

    Examples:
    - 'RistrettoPoint::compress(&self)' -> ('curve25519_dalek::ristretto::RistrettoPoint::compress', False)
    - 'elligator_ristretto_flavor(&FieldElement)' -> ('curve25519_dalek::ristretto::RistrettoPoint::elligator_ristretto_flavor', False)
    """
    # Extract base function name (remove parameters)
    base_name = func_name.split('(')[0].strip()

    # If it already has a type prefix (e.g., 'RistrettoPoint::compress')
    if '::' in base_name:
        type_and_func = base_name.split('::')
        if len(type_and_func) >= 2:
            type_name = type_and_func[0]
            func_name_only = type_and_func[-1]
            return (f"{module}::{type_name}::{func_name_only}", False)

    # No type prefix - need to infer it
    func_name_only = base_name

    # Try to get impl_block from functions_to_track if available
    if functions_to_track:
        key = f"{func_name},{module}"
        impl_block = functions_to_track.get(key, "")
        if impl_block and not any(trait in impl_block for trait in [' for ', '<', '>', 'From<', 'Add', 'Sub', 'Mul', 'Neg', 'Identity', 'Default', 'ConstantTimeEq', 'ConditionallySelectable']):
            # If it's a direct impl (not a trait), extract type name
            # impl_block might be like "RistrettoPoint" or empty
            if impl_block and not any(trait in impl_block for trait in [' for ', '<', '>']):
                return (f"{module}::{impl_block}::{func_name_only}", False)

    # Fallback: try to find from source code
    line_num = extract_line_number_from_link(link)
    if line_num:
        # Map module to source file path (try dalek-lite first, then main project)
        module_to_files = {
            'curve25519_dalek::ristretto': [
                'dalek-lite/curve25519-dalek/src/ristretto.rs',
                'curve25519-dalek/src/ristretto.rs'
            ],
            'curve25519_dalek::edwards': [
                'dalek-lite/curve25519-dalek/src/edwards.rs',
                'curve25519-dalek/src/edwards.rs'
            ],
            'curve25519_dalek::montgomery': [
                'dalek-lite/curve25519-dalek/src/montgomery.rs',
                'curve25519-dalek/src/montgomery.rs'
            ],
            'curve25519_dalek::scalar': [
                'dalek-lite/curve25519-dalek/src/scalar.rs',
                'curve25519-dalek/src/scalar.rs'
            ],
            'curve25519_dalek::field': [
                'dalek-lite/curve25519-dalek/src/field.rs',
                'curve25519-dalek/src/field.rs'
            ],
            'curve25519_dalek::backend::serial::u64::field': [
                'dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs',
                'curve25519-dalek/src/backend/serial/u64/field.rs'
            ],
            'curve25519_dalek::backend::serial::u64::scalar': [
                'dalek-lite/curve25519-dalek/src/backend/serial/u64/scalar.rs',
                'curve25519-dalek/src/backend/serial/u64/scalar.rs'
            ],
            'curve25519_dalek::backend::serial::curve_models': [
                'dalek-lite/curve25519-dalek/src/backend/serial/curve_models/mod.rs',
                'curve25519-dalek/src/backend/serial/curve_models/mod.rs'
            ],
        }

        file_paths = module_to_files.get(module, [])
        for file_path_str in file_paths:
            file_path = Path(file_path_str)
            if file_path.exists():
                type_name = find_impl_block_for_function(file_path, func_name_only, line_num)
                if type_name:
                    return (f"{module}::{type_name}::{func_name_only}", False)
                break

    # Last resort: return with module only (normalization failed)
    return (f"{module}::{func_name_only}", True)

def normalize_status_function_path(func_name: str) -> str:
    """
    Normalize a function path from status.csv (already in full format).
    Just return as-is since it's already normalized.
    """
    return func_name

def load_functions_to_track() -> Dict[str, str]:
    """Load impl_block information from functions_to_track.csv"""
    impl_blocks = {}
    track_file = Path('dalek-lite/functions_to_track.csv')
    if track_file.exists():
        with open(track_file, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                func = row['function']
                module = row['module']
                impl_block = row.get('impl_block', '')
                key = f"{func},{module}"
                impl_blocks[key] = impl_block
    return impl_blocks

def normalize_curve25519_functions_csv():
    """Add normalized_path and normalization_failed columns to curve25519_functions.csv"""
    input_file = Path('dalek-lite/outputs/curve25519_functions.csv')
    output_file = Path('dalek-lite/outputs/curve25519_functions_normalized.csv')

    if not input_file.exists():
        print(f"✗ Input file not found: {input_file}")
        return

    impl_blocks = load_functions_to_track()

    with open(input_file, 'r', encoding='utf-8') as infile, \
         open(output_file, 'w', encoding='utf-8', newline='') as outfile:

        reader = csv.DictReader(infile)
        fieldnames = list(reader.fieldnames) + ['normalized_path', 'normalization_failed']
        writer = csv.DictWriter(outfile, fieldnames=fieldnames)

        writer.writeheader()

        count = 0
        failed_count = 0
        for row in reader:
            func_name = row['function']
            module = row['module']
            link = row.get('link', '')

            normalized, is_fallback = normalize_curve25519_function_path(
                func_name, module, link, impl_blocks
            )

            row['normalized_path'] = normalized
            row['normalization_failed'] = 'True' if is_fallback else 'False'
            if is_fallback:
                failed_count += 1
            writer.writerow(row)
            count += 1

    print(f"✓ Created {output_file} with {count} normalized paths")
    if failed_count > 0:
        print(f"  ⚠ {failed_count} paths failed normalization (using fallback)")

def normalize_status_csv():
    """Add normalized_path column to status.csv"""
    input_file = Path('status.csv')
    output_file = Path('status_normalized.csv')

    if not input_file.exists():
        print(f"✗ Input file not found: {input_file}")
        return

    with open(input_file, 'r', encoding='utf-8') as infile, \
         open(output_file, 'w', encoding='utf-8', newline='') as outfile:

        reader = csv.DictReader(infile)
        fieldnames = list(reader.fieldnames) + ['normalized_path']
        writer = csv.DictWriter(outfile, fieldnames=fieldnames)

        writer.writeheader()

        count = 0
        for row in reader:
            func_name = row['function']
            normalized = normalize_status_function_path(func_name)
            row['normalized_path'] = normalized
            writer.writerow(row)
            count += 1

    print(f"✓ Created {output_file} with {count} normalized paths")

def main():
    print("Normalizing function paths in CSV files...")
    print()

    normalize_curve25519_functions_csv()
    normalize_status_csv()

    print()
    print("Done! You can now compare functions using the 'normalized_path' column.")
    print()
    print("Example comparison:")
    print("  curve25519_functions.csv: elligator_ristretto_flavor")
    print("  → normalized_path: curve25519_dalek::ristretto::RistrettoPoint::elligator_ristretto_flavor")
    print()
    print("  status.csv: curve25519_dalek::ristretto::RistrettoPoint::elligator_ristretto_flavor")
    print("  → normalized_path: curve25519_dalek::ristretto::RistrettoPoint::elligator_ristretto_flavor")

if __name__ == '__main__':
    main()

