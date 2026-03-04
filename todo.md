# Aeneas Update Status — Branch `update-aeneas-39e3086`

Remaining work: files with `sorry` that need proofs restored.

## Category A: Proofs broken by Aeneas update (had working proofs before)

These had complete proofs that broke with the Aeneas update. Old proofs are preserved
as block comments in the files. Main issues: `_post_N` → `_postN` naming, constants
(`ONE`, `ZERO`, `EDWARDS_D`, `EIGHT_TORSION`) now returning `Result`, tail call variable
naming changes, `UScalar.ofNat_val_eq` → `UScalar.ofNatCore_val_eq`.

### A1. Scalar52::add (Add.lean)

- **File**: `Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean`
- **Theorems**: `add_loop_spec`, `add_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: Old proof references `_post_1` style names, `ZERO` as value (now `Result`),
  `i5_post_1` naming. Looping proof with termination — needs careful rework.
- **Difficulty**: Medium-hard. Loop invariant proof with carry propagation.

### A2. Ristretto coset4 (Coset4.lean)

- **File**: `Specs/Ristretto/RistrettoPoint/Coset4.lean`
- **Theorem**: `coset4_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: `EIGHT_TORSION` now returns `Result`. Spec rewritten to use `eightTorsionPoints`.
  Old proof accessed `EIGHT_TORSION.val[i]` directly. Need to unfold the new `Result`-returning
  `EIGHT_TORSION` or use the new helpers.
- **Difficulty**: Medium. Mostly mechanical once EIGHT_TORSION access pattern is established.

### A3. MontgomeryReduce (MontgomeryReduce.lean)

- **File**: `Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean`
- **Theorems**: `part1_spec` (partial sorry at line 177), `montgomery_reduce_spec`
- **Marked**: `@[externally_verified, progress]` (main theorem)
- **Issue**: `part1_spec` has a sorry at the end — remaining `progress` calls after
  `constants.L` now returns `Result`. Main theorem had working proof but was commented
  out for slow build (8M heartbeats). The commented proof also needs updating for naming.
- **Difficulty**: Hard. Very long proof (650+ lines), polynomial arithmetic with `linear_combination`.

### A4. SqrtRatioi (SqrtRatioi.lean)

- **File**: `Specs/Field/FieldElement51/SqrtRatioi.lean`
- **Theorem**: `sqrt_ratio_i_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: 3 consecutive sorrys (lines 554-556). Proof was complete before Aeneas update.
  1500+ line file with extensive case analysis.
- **Difficulty**: Hard. Long proof needing systematic variable renaming + constant handling.

### A5. EdwardsPoint::is_small_order (IsSmallOrder.lean)

- **File**: `Specs/Edwards/EdwardsPoint/IsSmallOrder.lean`
- **Theorem**: `is_small_order_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: `ONE`/`ZERO` now return `Result`, `ONE_body`/`ZERO_body` removed.
  `ep_post_1`/`t_post_N`/`c_post` variable naming changed. `field_simp` calls may
  need updating.
- **Difficulty**: Medium. The proof structure is sound, mainly needs constant handling
  and variable renaming.

### A6. Ristretto CompressedRistretto::step_2 (Step2.lean)

- **File**: `Specs/Ristretto/CompressedRistretto/Step2.lean`
- **Theorem**: `step_2_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: `ONE`/`EDWARDS_D` now return `Result`. Progress variable naming cascade
  throughout the proof.
- **Difficulty**: Hard. Complex multi-step decompress proof.

### A7. Scalar52::Add sub_if_necessary (Add.lean, second theorem)

- **File**: `Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean`
- **Theorem**: `add_spec` (depends on `add_loop_spec`)
- **Issue**: Uses `ZERO` and `constants.L` which changed. Also references `res_post_1`,
  `sum_post_3` etc.
- **Difficulty**: Medium. Blocked by A1 (`add_loop_spec`).

## Category B: Proofs that need `progress*` fix (timeout/recursion issues)

These have proof attempts that fail due to `progress*` changes.

### B1. FieldElement51::pow22501 (Pow22501.lean)

- **File**: `Specs/Field/FieldElement51/Pow22501.lean`
- **Theorem**: `pow22501_spec`
- **Marked**: `@[progress]` (not externally_verified)
- **Issue**: Old proof used `progress*` followed by many bounds-discharge bullets
  referencing `t0_post_2`, `fe_post_2`, etc. These postcondition names likely changed.
  Also potential timeout issues with the deeply nested exponentiation chain.
- **Difficulty**: Medium. Systematic renaming of postcondition variables.

### B2. FieldElement51::pow_p58 (PowP58.lean)

- **File**: `Specs/Field/FieldElement51/PowP58.lean`
- **Theorem**: `pow_p58_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: `progress*` fails. Old proof references `__discr_post_3`, `t20_post_1`,
  `__discr_post_1`, `res_post_1`, `res_post_2`. Depends on `pow22501_spec` (B1).
- **Difficulty**: Medium. Depends on B1 being fixed first.

### B3. FieldElement51::invert (Invert.lean)

- **File**: `Specs/Field/FieldElement51/Invert.lean`
- **Theorem**: `invert_spec`
- **Marked**: `@[progress, externally_verified]`
- **Issue**: `progress*` fails. Old proof references `__discr_post_3/4`, `t20_post_1/2`,
  `res_post_1/2`. Depends on `pow22501_spec` (B1).
- **Difficulty**: Medium. Depends on B1 being fixed first.


## Priority order for fixing

1. **B1** (Pow22501) — unlocks B2 and B3
2. **A5** (IsSmallOrder) — relatively contained, medium difficulty
3. **A2** (Coset4) — mechanical, EIGHT_TORSION pattern
4. **A1** (Add) — important for scalar arithmetic chain
5. **B2** (PowP58) — after B1, relatively mechanical
6. **B3** (Invert) — after B1, relatively mechanical
7. **A3** (MontgomeryReduce part1) — complete the partial proof
8. **A6** (Step2) — Ristretto decompression
9. **A4** (SqrtRatioi) — large but systematic
