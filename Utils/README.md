# Utils

Utilities for analyzing the Curve25519Dalek verification project.

## CLI Tools

```bash
lake exe listfuns [output.json] [--all]  # List functions with deps & verification status
lake exe syncstatus [status.csv]          # Sync status.csv with discovered functions
```

## Library (`Utils.Lib`)

- `Types.lean` - `FunctionRecord` and JSON structures
- `ListFuns.lean` - Main pipeline: enumerate, filter, analyze functions
- `Analysis.lean` - Dependency and verification checking
- `Docstring.lean` - Parse Aeneas docstrings for source metadata
- `StatusCsv.lean` - CSV I/O for status tracking
