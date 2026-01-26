# Lean Profiling Tools

Scripts for profiling Lean file compilation times.

## Quick Start

```bash
# Profile specific files or folders
./scripts/bench/profile-lean.sh Curve25519Dalek/Specs/Field/

# Profile the whole project
./scripts/bench/profile-lean.sh --all

# View results
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json

# Save report to file
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json -o report.txt
```

## Scripts

| Script | Purpose |
|--------|---------|
| `profile-lean.sh` | Profile files with `lean --profile --json`, outputs JSON |
| `profile-report.sh` | Display/save profile results from JSON |
| `count-heartbeats.sh` | Quick tech debt scan via maxHeartbeats |

## Profiling

### Profile Files or Folders

```bash
# Single file
./scripts/bench/profile-lean.sh Curve25519Dalek/Specs/Field/FieldElement51/SqrtRatioi.lean

# Single folder
./scripts/bench/profile-lean.sh Curve25519Dalek/Specs/Backend/

# Multiple folders
./scripts/bench/profile-lean.sh Curve25519Dalek/Specs/ Curve25519Dalek/Proofs/

# All project files
./scripts/bench/profile-lean.sh --all
```

Output is saved to `benchmarks/profile-<timestamp>/`:
- `profile.json` - cumulative timing per file (overview)
- `details/` - per-definition JSON timing (for deep dives)
- `raw/` - raw `lean --profile --json` output

### View Profile Results

```bash
# Top 20 by simp time (default)
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json

# Top 10 by typeclass inference
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json --top 10 --by typeclass_inference_s

# Save to file
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json -o benchmarks/report.txt

# Available metrics: simp_s, typeclass_inference_s, import_s, elaboration_s,
#                    tactic_execution_s, grind_s, interpretation_s, parsing_s,
#                    type_checking_s, instantiate_metavars_s
```

## Tech Debt Detection

### Count maxHeartbeats

Files with high `maxHeartbeats` settings indicate elaboration complexity.

```bash
./scripts/bench/count-heartbeats.sh
```

Shows files with custom heartbeat limits and their values.

## Results Location

All results are saved to the `benchmarks/` directory:

```
benchmarks/
├── profile-20260121-143022/
│   ├── profile.json          # cumulative timing per file (overview)
│   ├── report.txt            # saved report (optional)
│   ├── details/              # per-definition timing (deep dive)
│   │   └── <file>.jsonl      # JSON lines with line/pos info
│   └── raw/                  # raw lean --profile --json output
```

## Understanding Profile Metrics

| Metric | Description |
|--------|-------------|
| `simp_s` | Time in simp tactic (often the biggest cost) |
| `typeclass_inference_s` | Time resolving typeclass instances |
| `grind_s` | Time in grind tactic |
| `import_s` | Time loading dependencies |
| `elaboration_s` | Total elaboration time |
| `tactic_execution_s` | Time executing tactics |

## Workflow

### Initial Baseline

```bash
# First time: profile entire project (can take hours)
nice -n 19 ./scripts/bench/profile-lean.sh --all

# Or profile in batches if needed
nice -n 19 ./scripts/bench/profile-lean.sh Curve25519Dalek/Specs/
nice -n 19 ./scripts/bench/profile-lean.sh Curve25519Dalek/Proofs/
```

### Per-PR Profiling

```bash
# Profile only changed files
nice -n 19 ./scripts/bench/profile-lean.sh path/to/changed/File.lean

# Compare with baseline
./scripts/bench/profile-report.sh benchmarks/profile-*/profile.json
```

### Deep Dive on Slow Files

```bash
# View per-definition timing for a slow file
cat benchmarks/profile-*/details/_Curve25519Dalek_Specs_Field_Pow2K_lean.jsonl | jq

# Shows which specific theorem/tactic calls are slow
# {"data":"simp took 1700s\n","pos":{"line":42},...}
```

## Tips

- Always run with `nice -n 19` to avoid system impact
- Project must be built first (`lake build`) for profiling
- For quick build timing, use `lake build -v` (no detailed breakdown)
- Import times are dominated by mathlib; focus on simp/typeclass for optimization
- Use `--by typeclass_inference_s` to find typeclass bottlenecks
- Use `details/*.jsonl` files to pinpoint exact slow proof steps
