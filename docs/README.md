# Curve25519-Dalek Documentation

This directory contains the Verso-Blueprint documentation for the Curve25519-Dalek Lean verification project.

## Building the Documentation

From the repository root, run:

```bash
./scripts/build-blueprint.sh
```

This will:
1. Build the `curve25519docs` executable
2. Generate HTML documentation in `_out/blueprint/html-multi/`

## Viewing Locally

After building, serve the documentation locally:

```bash
python3 -m http.server 8080 -d _out/blueprint/html-multi
```

Then open http://localhost:8080 in your browser.

## Directory Structure

- `Curve25519DalekDocsMain.lean` - Entry point for the docs executable
- `Curve25519DalekDocs.lean` - Library root
- `Curve25519DalekDocs/` - Documentation modules
  - `Contents.lean` - Main documentation content

## Adding Documentation

To add new documentation sections:

1. Create a new `.lean` file in `Curve25519DalekDocs/`
2. Import it in `Curve25519DalekDocs.lean`
3. Include it in `Contents.lean` using `{include 1 Curve25519DalekDocs.YourModule}`

See the [Verso documentation](https://github.com/leanprover/verso) for more details on the markup syntax.
