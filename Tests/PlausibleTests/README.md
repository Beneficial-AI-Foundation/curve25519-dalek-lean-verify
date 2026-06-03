# Tests

Property-based (Plausible) tests for curve25519-dalek Lean types.

This is a separate Lake library (`Tests` in `lakefile.toml`) that is **not** part of
`defaultTargets`. The tests therefore do **not** run on a normal `lake build` — keeping
the default build deterministic and fast.

Property tests are written as `example : P := by plausible`. The `plausible` tactic
samples the quantified variables: on finding a counter-example it errors and fails the
build; finding none, it closes the goal like `admit` (so each passing test emits a
`declaration uses 'sorry'` warning — that warning is the expected "passed" signal).

## Running

```sh
lake build Tests
```

This builds every module under `Tests/`, running the `plausible` property checks and the
`#check` instance smoke tests.

## Layout

- `Tests/PlausibleTests/ProbeTest.lean` — all Plausible tests:
  - instance smoke tests (`#check (inferInstance : …)`) confirming `Arbitrary`/`Shrinkable`/
    `SampleableExt` exist for every key type;
  - the signed scalar types (`I8`/`I16`/`I32`/`I64`/`Isize`) generate in-range values and
    arrays of them work;
  - `FieldElement51::add` against its spec, using bounded-subtype sampling
    (`{ a : Array U64 5 // ∀ i < 5, a[i]!.val < 2^53 }`) so the preconditions are satisfied
    by construction rather than by rejection sampling.

The instances under test live in `Curve25519Dalek/Plausible.lean`.

## Instance coverage (signed integers)

### `Arbitrary`
- `I8` → `[-128, 127]`
- `I16` → `[-32768, 32767]`
- `I32` → `[-2^31, 2^31-1]`
- `I64` → `[-2^63, 2^63-1]`
- `Isize` → `[-2^63, 2^63-1]`

Each generator biases toward edge cases (85% random, 5% zero, 5% min, 5% max).

### `Shrinkable`
`I8`/`I16`/`I32`/`I64`/`Isize` shrink toward 0 from both directions by halving the
absolute value and preserving the sign (`BitVec.ofInt` for the Int→BitVec conversion,
with concrete per-type bounds to avoid proof obligations).
