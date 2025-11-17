#!/usr/bin/env python3
"""
Extract all function and constant paths from rustdoc JSON output.
Usage: python3 extract_items.py target/doc/curve25519_dalek.json
"""

import json
import sys
from collections import defaultdict

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 extract_items.py <rustdoc_json_file>", file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1], 'r') as f:
        data = json.load(f)

    index = data['index']
    paths = data['paths']

    # Build a map of type IDs to their paths for associating methods
    type_paths = {}
    for item_id, path_info in paths.items():
        type_paths[item_id] = '::'.join(path_info['path'])

    # Collect all items
    results = []

    for item_id, item in index.items():
        inner = item.get('inner', {})

        # The kind is actually a key in the inner dict
        if 'function' in inner:
            if item_id in paths:
                results.append('::'.join(paths[item_id]['path']))

        elif 'constant' in inner:
            if item_id in paths:
                results.append('::'.join(paths[item_id]['path']))

        elif 'method' in inner:
            if item_id in paths:
                results.append('::'.join(paths[item_id]['path']))

        elif any(k in inner for k in ['struct', 'enum', 'union']):
            # Look for associated impls
            struct_or_enum = inner.get('struct') or inner.get('enum') or inner.get('union')
            if struct_or_enum and 'impls' in struct_or_enum:
                # Get the base path for this type
                if item_id in paths:
                    type_path = '::'.join(paths[item_id]['path'])
                else:
                    continue

                for impl_id in struct_or_enum['impls']:
                    # Convert to string as index keys are strings
                    impl_id_str = str(impl_id)
                    if impl_id_str in index:
                        impl_item = index[impl_id_str]
                        impl_inner = impl_item.get('inner', {})

                        if 'impl' in impl_inner:
                            impl_data = impl_inner['impl']
                            # Check if this is an inherent impl (no trait) or a trait impl
                            is_inherent = impl_data.get('trait') is None

                            if 'items' in impl_data:
                                for method_id in impl_data['items']:
                                    method_id_str = str(method_id)
                                    # Check if in paths first
                                    if method_id_str in paths:
                                        results.append('::'.join(paths[method_id_str]['path']))
                                    # Otherwise construct the path manually
                                    elif method_id_str in index:
                                        method_item = index[method_id_str]
                                        method_inner = method_item.get('inner', {})
                                        # Only include functions/methods/constants, skip associated types
                                        if any(k in method_inner for k in ['function', 'method', 'constant']):
                                            method_name = method_item.get('name')
                                            if method_name and is_inherent:
                                                # Only include inherent methods (not trait impls)
                                                # Construct Type::method path
                                                results.append(f"{type_path}::{method_name}")

        elif 'impl' in inner:
            # Standalone impl blocks
            impl_data = inner['impl']
            if 'items' in impl_data:
                for impl_item_id in impl_data['items']:
                    impl_item_id_str = str(impl_item_id)
                    if impl_item_id_str in paths:
                        results.append('::'.join(paths[impl_item_id_str]['path']))

    # Sort and deduplicate
    results = sorted(set(results))

    # Print results
    for path in results:
        print(path)

if __name__ == '__main__':
    main()
