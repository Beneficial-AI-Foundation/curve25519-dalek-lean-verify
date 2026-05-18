# Specs/Backend — Remaining `streamline_prompt` Violations

**Date of audit:** 2026-05-18
**Branch:** `streamline_styles_backend`
**Method:** Each previously-flagged file (from `STREAMLINE_AUDIT.md`) was re-read in full and judged against `streamline_prompt`. Four categories from the prior audit were treated as non-violations per the audit's filter rationale:

1. Files dated 2025 keep year 2025.
2. Module docstring may drop `#` if needed to keep title ≤100 chars.
3. Spec docstring may drop `**...**` bold if needed to keep title ≤100 chars.
4. Spec docstring bullets may use `•` at the first level and `-` at the second (nested) level — this is the intended convention, not a violation.

Files that were flagged solely on these four categories are now clean.

## Summary

| Bucket | Re-audited | Now clean | Remaining |
|---|---|---|---|
| CurveModels + ScalarMul + Backend root | 16 | 8 | 8 |
| U64/Scalar | 16 | 6 | 10 |
| U64/Constants + FieldElement51 | 15 | 11 | 4 |
| **Total** | **47** | **25** | **22** |

Out of all 83 files in `Curve25519Dalek/Specs/Backend/`, ~61 are fully clean and ~22 still have residual style issues — most of them minor.

## Remaining violations


### CurveModels (8)

| File | Remaining issue |
|---|---|
| `Serial/CurveModels/AffineNielsPoint/AssertReceiverIsTotalEq.lean` | Typo `curve25519_daleK` (capital K) in title and spec path |
| `Serial/CurveModels/AffineNielsPoint/ConditionalAssign.lean` | Spec docstring path drops `curve25519_dalek::` prefix |
| `Serial/CurveModels/AffineNielsPoint/Add.lean` | Title path says `CompletedPoint::add` in folder `AffineNielsPoint/`; spec docstring missing crate prefix |
| `Serial/CurveModels/ProjectiveNielsPoint/Neg.lean` | Second spec docstring path missing `curve25519_dalek::` prefix |
| `Serial/CurveModels/ProjectiveNielsPoint/ConditionalAssign.lean` | Second spec docstring has trailing `:` after bolded title; missing full path |
| `Serial/CurveModels/ProjectivePoint/Double.lean` | First spec missing `curve25519_dalek::` prefix; `set_option linter.hashCommand false` suppression |
| `Serial/CurveModels/CompletedPoint/AsExtended.lean` | Spec docstring missing `curve25519_dalek::` prefix |
| `Serial/CurveModels/CompletedPoint/Add.lean` | Main `add_spec` uses numbered (1./2./3.) list instead of `•` bullets |

### U64/Scalar (10)

| File | Remaining issue |
|---|---|
| `Serial/U64/Scalar/Scalar52/Sub.lean` | First spec (`sub_loop_spec`) uses prose/equations instead of `•` bullets |
| `Serial/U64/Scalar/Scalar52/FromMontgomery.lean` | First spec docstring title uses informal `**Spec theorem for the inner loop...**` form, not full Rust path |
| `Serial/U64/Scalar/Scalar52/SquareInternal.lean` | Leftover central comment block (lines 46–51) duplicates module docstring info |
| `Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean` | Active line 57 = 116 chars (>100); module docstring drops `#` even though title fits with `#` |
| `Serial/U64/Scalar/Scalar52/AsMontgomery.lean` | `set_option` placed between imports and module docstring |
| `Serial/U64/Scalar/Scalar52/ConditionalAddL.lean` | `attribute [-simp]` and `set_option` between imports and docstring; `namespace` before `open` (inverted) |
| `Serial/U64/Scalar/Scalar52/ToBytes.lean` | Two blank lines between module docstring end and `open` |
| `Serial/U64/Scalar/Scalar52/SquareMultiply.lean` | First spec (`square_multiply_loop_spec`) uses prose paragraph instead of `**Spec theorem for ...**` + `•` bullets |
| `Serial/U64/Scalar/Scalar52/MontgomeryInvert.lean` | Module + spec path say `curve25519_dalek::backend::scalar::Scalar52::...` — extra `backend::` shouldn't be there (Source is `src/scalar.rs`); blank line + `set_option` between last `open` and `namespace` |
| `Serial/U64/Scalar/Scalar52/MontgomerySquare.lean` | Module docstring drops `#` even though title fits with `#` (exactly 100 chars) |

### U64/Constants (1)

| File | Remaining issue |
|---|---|
| `Serial/U64/Constants/OneMinusEdwardsDSquared.lean` | Both module and spec docstring paths drop `curve25519_dalek::` even though the full path fits |

### U64/Field/FieldElement51 (3)

| File | Remaining issue |
|---|---|
| `Serial/U64/Field/FieldElement51/ToBytes.lean` | Line 260 = 105 chars (>100) |
| `Serial/U64/Field/FieldElement51/FromBytes.lean` | `namespace` appears BEFORE `open Aeneas Aeneas.Std Result Aeneas.Std.WP` (inverted order) |
| `Serial/U64/Field/FieldElement51/Mul.lean` | Main `mul_spec` docstring uses one descriptive sentence, no `•` bulleted post-condition list |

## Priority queue (substantive issues, fix first)

The remaining violations are mostly cosmetic. The ones that are substantively wrong:

1. **`Scalar52/MontgomeryInvert.lean`** — wrong module path (`::backend::scalar::` should be `::scalar::`).
2. **`Scalar52/MontgomeryReduce.lean`** — active line 57 exceeds 100 chars (linter-relevant).
3. **`FieldElement51/FromBytes.lean`** — `namespace` before `open` (inverted order; may affect resolution).
4. **`Scalar52/ConditionalAddL.lean`** — same `namespace`/`open` inversion; plus `attribute`/`set_option` misplaced.
5. **Prose-instead-of-bullets** in `Scalar52/Sub.lean`, `Scalar52/SquareMultiply.lean`, `FieldElement51/Mul.lean`, `CompletedPoint/Add.lean` — docstring structure deviates from the standard `•` post-condition list.
6. **`AffineNielsPoint/Add.lean`** — title path references `CompletedPoint::add` while the file lives in `AffineNielsPoint/`.

Everything else (missing `curve25519_dalek::` prefix, typo `daleK`, stray blank lines, leftover central comment block) is small-scale cosmetic cleanup.
