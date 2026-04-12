# Proof Analysis: curve25519-dalek Lean 4 Specification Theorems

## Overview

This analysis covers all `@[step] theorem` declarations in the `Curve25519Dalek/Specs/` directory.
These are specifications and proofs about Rust functions from the curve25519-dalek crate,
translated to Lean 4 via Aeneas.

### Summary Statistics

| Metric | Count |
|--------|-------|
| **Total `@[step]` theorems** | ~155 |
| **Complete proofs** | ~146 |
| **Proofs with `sorry`** | 9 |
| **Files in Specs directory** | 158 |
| **Total lines of proof code** | ~25,000+ |

### Completion by Domain

| Domain | Complete | Sorry | Total |
|--------|----------|-------|-------|
| field_arithmetic | 30 | 0 | 30 |
| scalar_arithmetic | 38 | 0 | 38 |
| curve_operations | 32 | 5 | 37 |
| serialization | 22 | 0 | 22 |
| conditional | 14 | 0 | 14 |
| comparison | 12 | 0 | 12 |
| identity | 16 | 0 | 16 |
| montgomery | 11 | 1 | 12 |

### Complexity Distribution

| Complexity | Count | Percentage |
|------------|-------|------------|
| trivial | ~55 | ~35% |
| simple | ~40 | ~26% |
| moderate | ~35 | ~23% |
| complex | ~25 | ~16% |

## Incomplete Proofs (sorry)

These 9 theorems remain incomplete:

| File | Theorem | Status | Notes |
|------|---------|--------|-------|
| Edwards/EdwardsPoint/Mul.lean | mul_spec (core) | `externally_verified` | Proven in Verus, core variable-base scalar multiplication |
| Edwards/EdwardsPoint/MulBase.lean | mul_base_spec | `externally_verified` | Proven in Verus, basepoint scalar multiplication |
| Edwards/EdwardsPoint/MulByPow2.lean | mul_by_pow_2_spec | `externally_verified` | Proven in Verus, repeated doubling loop |
| Edwards/EdwardsPoint/Compress.lean | compress_spec | `externally_verified` | Placeholder True spec |
| Edwards/CompressedEdwardsY/Step1.lean | step_1_spec | incomplete | Decompression step 1: y recovery + x^2 computation |
| Edwards/CompressedEdwardsY/Decompress.lean | decompress_spec | incomplete | Full decompression, depends on Step1 |
| Edwards/Affine/AffinePoint/Compress.lean | compress_spec | incomplete | Placeholder True spec |
| Montgomery/MontgomeryPoint/Mul.lean | mul_loop_spec | incomplete | Montgomery ladder loop, 3 sorry cases in induction |
| Scalar/Scalar/AsRadix16.lean | as_radix_16_loop1_spec | partial | One `inv_step_loop1` sorry in helper |

Of these, 4 are intentionally marked `@[externally_verified]` (proven in Verus), leaving **5 genuinely incomplete proofs**.

## Proof Technique Analysis

### Technique Frequency

| Technique | Occurrences | Notes |
|-----------|-------------|-------|
| `step*_only` | ~40 | step* closes entire proof |
| `step*_plus_bullets` | ~100 | step* + manual side goals |
| `manual_lemmas` | ~50 | `have` lemmas within proof |
| `modular_arithmetic` | ~35 | Nat.ModEq reasoning |
| `arithmetic` | ~20 | nlinarith, omega bounds |
| `scalar_tac_heavy` | ~15 | Heavy use of scalar_tac |
| `fold_decomposition` | ~8 | Helper + fold + main pattern |
| `bit_manipulation` | ~12 | bvify, bv_decide, shifts |
| `bitlist_conversion` | ~8 | BitList representation |
| `structure_unfolding` | ~20 | IsValid, toPoint unfolding |
| `interval_cases` | ~10 | Case analysis on indices |
| `simp_lists` | ~3 | simp_lists for array reasoning |
| `expand_array` | ~2 | expand_array tactic |
| `array_manipulation` | ~8 | .set/.update chains |

### Pattern: Fold Theorem Decomposition

The most complex proofs use a **fold decomposition** pattern, found in:
- `FieldElement51.Mul` (3 stages: product, carry propagation, final reduction)
- `FieldElement51.Pow2K` (3 stages: squaring, carry propagation, final reduction)
- `Scalar52.MontgomeryReduce` (part1, part2, main)

The pattern:
1. Define helper functions (`square_stage`, `carry_prop_stage`, `final_reduce_stage`)
2. Prove fold lemmas that rewrite the monadic code into helper calls
3. Prove `@[step]` specs for each helper
4. In the main proof, `simp_rw [fold_*]` then `step*` applies helper specs

This is the most effective approach for functions with 50+ monadic operations.

### Pattern: Exponent Chain

Used in `Pow22501`, `PowP58`, `Invert`, `MontgomeryInvert`:
- Chain lemmas: `chain_sq`, `chain_mul`, `chain_pow2k`
- Each operation extends the exponent: `step with <spec> as ...`
- Compose via `Nat.ModEq.trans`
- Final exponent verified by kernel reduction

### Pattern: BitList Conversion

Used in `FromBytes` and `ToBytes_C`:
- Translate byte operations to `List Bool` operations
- Prove equivalence (`BitList.Equiv`) between bit extractions
- Bridge back to `Nat` values via `toNat_ofU64`

## Domain Analysis

### Field Arithmetic (30 specs)

**Location**: `Backend/Serial/U64/Field/FieldElement51/` and `Field/FieldElement51/`

The most technically challenging domain. Key challenges:
- **Mul/Pow2K**: 893/836 lines respectively. Require fold decomposition to manage
  80+ monadic operations. The `decompose` lemma (25-term polynomial identity mod p)
  is critical.
- **Reduce**: Uses `simp_lists` and `expand_array` for array manipulation.
- **ToBytes**: 720 lines, the largest single-function proof. Byte packing with
  overlapping limb boundaries requires `bvify`/`bv_decide` for shift/mask reasoning.
- **FromBytes**: Uses BitList abstraction to cleanly express bit extraction.

All field arithmetic proofs are **complete**.

### Scalar Arithmetic (38 specs)

**Location**: `Backend/Serial/U64/Scalar/Scalar52/` and `Scalar/Scalar/`

Similar patterns to field arithmetic but with the group order L instead of p.
Key files:
- **MontgomeryReduce**: 909 lines, the largest spec file by line count.
  5-iteration Montgomery reduction with carry chains.
- **MulInternal/SquareInternal**: Schoolbook multiplication, closed by `ring` + `interval_cases`.
- **Add/Sub loops**: Carry/borrow propagation with loop induction.

All scalar arithmetic proofs are **complete**.

### Curve Operations (37 specs)

**Location**: `Backend/Serial/CurveModels/`, `Edwards/EdwardsPoint/`, `Ristretto/RistrettoPoint/`

The hierarchy of point representations:
```
EdwardsPoint (extended: X,Y,Z,T)
  -> ProjectivePoint (X,Y,Z)
  -> AffineNielsPoint (y+x, y-x, 2dxy)
  -> ProjectiveNielsPoint (Y+X, Y-X, 2dXY, 2Z)
  -> CompletedPoint (X,Y,Z,T intermediate form)
```

Key challenges:
- **CompletedPoint.Add**: 788 lines. The unified addition formula verification.
- **ProjectiveNielsPoint.Sub**: 664 lines. Subtraction in completed coordinates.
- **ProjectivePoint.Double**: 352 lines. Doubling formulas.
- **ElligatorRistrettoFlavor**: 1551 lines. Most complex single spec file.
- **RistrettoPoint.Compress**: 565 lines. Ristretto encoding.

These proofs require extensive `structure_unfolding` of `IsValid` and `toPoint`,
and connect the limb-level computations to abstract curve point operations.

**5 proofs incomplete**: Core scalar multiplication (`mul`, `mul_base`, `mul_by_pow_2`)
are marked `externally_verified` (Verus). `compress` and `decompress` have placeholder specs.

### Montgomery (12 specs)

**Location**: `Montgomery/MontgomeryPoint/`, `Montgomery/ProjectivePoint/`

- **DifferentialAddAndDouble**: 458 lines. Core Montgomery ladder step.
- **ElligatorEncode**: 771 lines. Elligator encoding for Montgomery points.
- **ToEdwards**: 323 lines. Birational equivalence conversion.
- **mul_loop_spec**: The one genuinely incomplete Montgomery proof. Induction on
  the Montgomery ladder loop has 3 sorry cases.

### Serialization (22 specs)

Serialization proofs span field elements, scalars, and point encodings.
The main challenge is byte packing/unpacking with bit-level operations.
All complete.

### Conditional/Comparison/Identity (~42 specs)

These are generally simple: `conditional_select`, `conditional_assign`, `ct_eq`, `eq`,
`identity`. Most are trivial or simple, resolved by `step*` alone or with
minor by-cases reasoning.

## Largest Proofs (by file size)

| File | Lines | Domain | Key Challenge |
|------|-------|--------|---------------|
| Field/FieldElement51/SqrtRatioi.lean | 1580 | field_arithmetic | Square root ratio with many helper lemmas |
| Ristretto/RistrettoPoint/ElligatorRistrettoFlavor.lean | 1551 | curve_operations | Ristretto elligator encoding |
| Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean | 909 | scalar_arithmetic | 5-iteration Montgomery reduction |
| Backend/Serial/U64/Field/FieldElement51/Mul.lean | 893 | field_arithmetic | Field multiplication (fold decomposition) |
| Scalar/Scalar/AsRadix16.lean | 839 | scalar_arithmetic | Radix-16 conversion with loops |
| Backend/Serial/U64/Field/FieldElement51/Pow2K.lean | 836 | field_arithmetic | Iterated squaring (fold decomposition) |
| Backend/Serial/CurveModels/CompletedPoint/Add.lean | 788 | curve_operations | Unified addition formula |
| Montgomery/MontgomeryPoint/ElligatorEncode.lean | 771 | montgomery | Elligator encoding |
| Backend/Serial/U64/Field/FieldElement51/ToBytes.lean | 720 | serialization | Byte packing with overlapping limbs |
| Backend/Serial/CurveModels/ProjectiveNielsPoint/Sub.lean | 664 | curve_operations | Subtraction in completed coordinates |

## Recommendations

### Proofs that could benefit from new tactics

1. **Array update chains** (ToBytes, CompletedPoint.Add, ProjectiveNielsPoint.Sub):
   These proofs spend hundreds of lines on `Array.set_of_ne_getElem!` reasoning.
   A dedicated tactic for proving properties of arrays after multiple updates
   would dramatically reduce proof sizes.

2. **Carry chain reasoning** (Mul, Pow2K, MontgomeryReduce):
   The pattern of `a'[i] = c_i % 2^51` and `carry = c_i / 2^51` with
   `Field51_as_Nat result + carry * p = original` is repeated in several proofs.
   A specialized tactic or automation for carry-chain conservation would help.

3. **Structure-level IsValid propagation** (all curve operation proofs):
   Proving that results satisfy `IsValid` after operations requires repeating
   bounds checks for each coordinate. Automation that propagates IsValid through
   field operations would simplify curve proofs.

4. **Modular arithmetic chains** (Pow22501, Invert, PowP58):
   The `chain_sq`/`chain_mul`/`chain_pow2k` pattern is already well-factored
   but could be automated into a tactic that verifies exponent chains.

### Priority for completing incomplete proofs

1. **Montgomery ladder loop** (`MontgomeryPoint/Mul.lean`): This is the most
   impactful incomplete proof, as it blocks full verification of X25519 key exchange.
   The 3 sorry cases in the induction need careful invariant maintenance.

2. **CompressedEdwardsY decompression** (Step1, Decompress): These block
   full signature verification. Step1 requires proving the curve equation
   after square root recovery.

3. **AffinePoint/EdwardsPoint compress**: Currently placeholder specs.
   Need proper spec statements before proof can proceed.
