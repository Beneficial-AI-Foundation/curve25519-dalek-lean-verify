# Utils

Command-line utilities for analyzing the Curve25519Dalek verification project.

## Executables

### listfuns

Lists all functions defined in `Curve25519Dalek/Funs.lean`.

```bash
lake exe listfuns [output.json]
```

**Arguments:**
- `[output.json]` - Output file (prints to stdout if omitted)

**Output format:**
```json
{
  "functions": [
    { "lean_name": "curve25519_dalek.some.function" },
    ...
  ]
}
```

**Filtering:**
- Excludes `core.*` and `subtle.*` namespaces
- Excludes internal suffixes (`_body`, `_loop`)
- Excludes nested functions (internal helpers defined within other functions)

---

### deps

Analyzes functions for verification status and dependencies.

```bash
lake exe deps <input.json> [output.json]
```

**Arguments:**
- `<input.json>` - JSON file with functions to analyze (same format as `listfuns` output)
- `[output.json]` - Output file (prints to stdout if omitted)

**Output format:**
```json
{
  "functions": [
    {
      "lean_name": "curve25519_dalek.some.function",
      "dependencies": ["dep1", "dep2"],
      "specified": true,
      "verified": true,
      "fully_verified": false
    },
    ...
  ]
}
```

**Output fields:**
- `dependencies` - Other functions from the input set that this function depends on
- `specified` - `true` if a theorem `{lean_name}_spec` exists
- `verified` - `true` if specified AND the spec theorem's proof contains no `sorry`
- `fully_verified` - `true` if verified AND all transitive dependencies are also verified

**Example workflow:**
```bash
lake exe listfuns functions.json
lake exe deps functions.json analysis.json
```

---

### syncstatus

Synchronizes `status.csv` with functions from `Funs.lean`. Adds new rows for any functions not already tracked.

```bash
lake exe syncstatus [status.csv]
```

**Arguments:**
- `[status.csv]` - Path to status file (default: `status.csv`)

**Behavior:**
1. Reads the current `status.csv`
2. Extracts all function definitions from `Funs.lean`
3. Identifies functions not yet in `status.csv`
4. Adds new rows for missing functions (with `lean_name` and `function` fields populated)

## Supporting Modules

- **ListFuns.lean** - Core logic for extracting function definitions from the Lean environment
- **StatusCsv.lean** - CSV parsing and writing utilities for `status.csv`
- **Analysis.lean** - Dependency analysis logic (traversing expressions, checking for `sorry`, computing transitive dependencies)
- **Json.lean** - JSON input/output structures and parsing utilities
