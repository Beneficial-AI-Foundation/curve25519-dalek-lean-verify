# Setting Up Verso-Blueprint 

This guide explains how to set up Verso-Blueprint documentation for a Lean 4 project.

## Prerequisites

- A working Lean 4 project with `lakefile.toml`
- `elan` installed

## Directory Structure

```
your-project/
├── lakefile.toml          # Main project lakefile
├── lean-toolchain
├── YourLib/               # Your Lean source files
│   └── *.lean
└── docs/
    ├── lakefile.toml      # Docs project lakefile
    ├── lean-toolchain
    ├── Main.lean
    └── YourDocs/          # Documentation source files
        └── *.lean
```

## Step 1: Set Up the Docs Project

Create `docs/lakefile.toml`:

```toml
name = "YourDocs"
defaultTargets = ["YourDocs", "docs"]

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "main"  # or a specific commit

[[lean_lib]]
name = "YourDocs"

[[lean_exe]]
name = "docs"
root = "Main"
```

Create `docs/lean-toolchain` with the same Lean version as your main project.

## Step 2: Build the Docs Project

```bash
cd docs
lake build
```

This will fetch Verso and its dependencies, including `subverso`.

## Step 3: Add Subverso to the Main Project

Look up the `subverso` commit from `docs/lake-manifest.json`:

```bash
grep -A2 '"name": "subverso"' docs/lake-manifest.json
```

Add `subverso` (not `verso`) to your main project's `lakefile.toml`:

```toml
[[require]]
name = "subverso"
git = "https://github.com/leanprover/subverso"
rev = "<commit-from-lake-manifest>"
```

## Step 4: Build the Main Project

Build with `--keep-toolchain` to prevent the lean-toolchain from updating to subverso's version:

```bash
lake build --keep-toolchain
```

## Step 5: Configure Example Project Path

In your documentation Lean files, set the `verso.exampleProject` option to point to your main project:

```lean
set_option verso.exampleProject "."
```

The path is relative to the workspace root when running `lake -d docs build` from the main project directory.

## Building Documentation

From the main project root:

```bash
lake -d docs build docs
```

Or create a build script (e.g., `scripts/build-blueprint.sh`):

```bash
#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

out_root="${1:-_out/blueprint}"
mkdir -p "$out_root"

lake -d docs build docs
"docs/.lake/build/bin/docs" --output "$out_root"

echo "Output: $(readlink -f "$out_root")"
```

## Serving the Documentation

```bash
python3 -m http.server 8080 -d _out/blueprint
```

Then open http://localhost:8080 in your browser.
