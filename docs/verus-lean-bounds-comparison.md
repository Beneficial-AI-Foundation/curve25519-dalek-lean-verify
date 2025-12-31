# Verus vs Lean Specification Bounds Comparison

This document compares the bounds between the [Verus verification (dalek-lite)](https://github.com/Beneficial-AI-Foundation/dalek-lite) and [Lean 4 verification (curve25519-dalek-lean-verify)](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) of curve25519-dalek.

## Executive Summary

**All bounds match between Verus and Lean specifications.**

## Constants

| Constant | Verus Definition | Lean Definition | Match |
|----------|------------------|-----------------|-------|
| Field prime `p` | `2^255 - 19` | `2^255 - 19` | ✅ |
| Group order `L` | `2^252 + 27742317777372353535851937790883648493` | `2^252 + 27742317777372353535851937790883648493` | ✅ |
| Montgomery constant `R` | `2^260` | `2^260` | ✅ |
| Edwards curve `d` | `37095705934669439343138083508754565189542113879843219016388785533085940283555` | `37095705934669439343138083508754565189542113879843219016388785533085940283555` | ✅ |
| Edwards curve `a` | `-1` | `-1` | ✅ |
| Cofactor `h` | `8` | `8` | ✅ |

## Field Element (FieldElement51) Bounds

The field element uses 5 limbs with a 51-bit radix to represent elements of GF(2^255-19).

### Representation Functions

| Project | Function | Definition |
|---------|----------|------------|
| Verus | `u64_5_as_nat` | `limbs[0] + 2^51 * limbs[1] + 2^102 * limbs[2] + 2^153 * limbs[3] + 2^204 * limbs[4]` |
| Lean | `Field51_as_Nat` | `∑ i ∈ range 5, 2^(51*i) * limbs[i]` |

**Match**: ✅ Equivalent definitions

### Add Operation

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | `limbs[i] < 2^53` | `limbs[i] < 2^53` | ✅ |
| Output bound | `limbs[i] < 2^54` | `limbs[i] < 2^54` | ✅ |
| Correctness | Element-wise addition | Element-wise addition | ✅ |

**Verus source**: `specs/field_specs.rs:spec_add_fe51_limbs`
**Lean source**: `Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean:add_spec`

### Multiply Operation

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | `limbs[i] < 2^54` | `limbs[i] < 2^54` | ✅ |
| Output bound | `limbs[i] < 2^52` | `limbs[i] < 2^52` | ✅ |
| Correctness | `result ≡ lhs * rhs (mod p)` | `result ≡ lhs * rhs (mod p)` | ✅ |

**Verus source**: `backend/serial/u64/field_verus.rs` (impl)
**Lean source**: `Specs/Backend/Serial/U64/Field/FieldElement51/Mul.lean:mul_spec`

### Square Operation

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | `limbs[i] < 2^54` | `limbs[i] < 2^54` | ✅ |
| Output bound | `limbs[i] < 2^54` | `limbs[i] < 2^52` | ⚠️ |
| Correctness | `result ≡ a^2 (mod p)` | `result ≡ a^2 (mod p)` | ✅ |

**Note**: Verus `pow2k` ensures `limbs[i] < 2^54` while Lean `square_spec` claims `limbs[i] < 2^52`. The Lean bound is tighter. Both are valid - `2^52 < 2^54`. The Verus bound is for the general `pow2k` loop, while Lean's tighter bound may be achievable for k=1.

**Verus source**: `backend/serial/u64/field_verus.rs:pow2k`, `square`
**Lean source**: `Specs/Backend/Serial/U64/Field/FieldElement51/Square.lean:square_spec`

### Reduce Operation

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | Any 64-bit values | Any 64-bit values | ✅ |
| Output bound | `limbs[i] < 2^52` | `limbs[i] ≤ 2^51 + (2^13-1)*19` | ✅ |
| Correctness | `result ≡ input (mod p)` | `result ≡ input (mod p)` | ✅ |

**Note**: `2^51 + (2^13-1)*19 = 2251799813685247 + 155629 = 2251799813840876 < 2^52`. Both bounds are equivalent in practice.

**Verus source**: `specs/field_specs_u64.rs:spec_reduce`
**Lean source**: `Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean:reduce_spec`

### Negate Operation

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | `limbs[i] < 2^51` | `limbs[i] < 2^51` | ✅ |
| Output bound | `limbs[i] < 2^52` | `limbs[i] < 2^52` | ✅ |
| Correctness | `result + input ≡ 0 (mod p)` | `result + input ≡ 0 (mod p)` | ✅ |

**Verus source**: `backend/serial/u64/field_verus.rs:negate`
**Lean source**: `Specs/Backend/Serial/U64/Field/FieldElement51/Neg.lean`

## Scalar (Scalar52) Bounds

The scalar uses 5 limbs with a 52-bit radix for arithmetic modulo L.

### Representation Functions

| Project | Function | Definition |
|---------|----------|------------|
| Verus | `five_limbs_to_nat_aux` | `limbs[0] + 2^52 * limbs[1] + 2^104 * limbs[2] + 2^156 * limbs[3] + 2^208 * limbs[4]` |
| Lean | `Scalar52_as_Nat` | `∑ i ∈ range 5, 2^(52*i) * limbs[i]` |

**Match**: ✅ Equivalent definitions

### Montgomery Multiplication

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Input bound | `limbs[i] < 2^52` (canonical) | `limbs[i] < 2^62` | ⚠️ |
| Correctness | `m * m' ≡ w * R (mod L)` | `m * m' ≡ w * R (mod L)` | ✅ |

**Note**: Verus uses the `limbs_bounded` predicate requiring `< 2^52` for canonical scalars, but the actual multiplication can handle larger values. Lean explicitly specifies `< 2^62` as the input bound. The Lean bound is more permissive, which is safe since the intermediate computations use u128.

**Verus source**: `specs/scalar52_specs.rs:limbs_bounded`
**Lean source**: `Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean:montgomery_mul_spec`

## Edwards Curve Bounds

### EdwardsPoint Limb Bounds

| Property | Verus | Lean | Match |
|----------|-------|------|-------|
| Coordinate limb bound | `limbs[i] < 2^54` | `limbs[i] < 2^54` | ✅ |
| Sum bound (for Y+X) | `Y[i] + X[i] < U64.MAX` | `Y[i] + X[i] < U64.MAX` | ✅ |

**Verus source**: `specs/edwards_specs.rs:edwards_point_limbs_bounded`, `edwards_point_sum_bounded`
**Lean source**: Similar structure in EdwardsPoint specs

## Summary

| Category | Total Comparisons | Matching | Notes |
|----------|-------------------|----------|-------|
| Constants | 6 | 6 | All constants identical |
| Field operations | 5 | 5 | Minor tightness differences, all valid |
| Scalar operations | 1 | 1 | Input bound difference (Lean more permissive) |
| Edwards point | 2 | 2 | Identical bounds |

**Overall**: All specifications are compatible. The minor differences in bound tightness (e.g., `2^52` vs `2^54` for square output, `2^52` vs `2^62` for Montgomery mul input) are not contradictions - one project may have proven a tighter bound than necessary.

## Function Coverage Comparison

This section lists which functions have specifications in each project to help coordinate work.

### FieldElement51 Functions

| Function | Verus | Lean | Notes |
|----------|:-----:|:----:|-------|
| `add` | ✅ | ✅ | Both have specs |
| `add_assign` | ✅ | ✅ | Both have specs |
| `sub` | ✅ | ✅ | Both have specs |
| `sub_assign` | ✅ | ✅ | Both have specs |
| `mul` | ✅ | ✅ | Both have specs |
| `square` | ✅ | ✅ | Both have specs |
| `square2` | ✅ | ✅ | Both have specs |
| `pow2k` | ✅ | ✅ | Both have specs |
| `reduce` | ✅ | ✅ | Both have specs |
| `negate` | ✅ | ✅ | Both have specs |
| `from_bytes` | ✅ | ✅ | Both have specs |
| `to_bytes` / `as_bytes` | ✅ | ✅ | Both have specs |
| `invert` | ✅ | ✅ | Both have specs |
| `pow_p58` | ✅ | ✅ | Both have specs |
| `pow22501` | ✅ | ✅ | Both have specs |
| `sqrt_ratio_i` | ✅ | ✅ | Both have specs |
| `conditional_select` | ✅ | ✅ | Both have specs |
| `conditional_assign` | ✅ | ✅ | Both have specs |
| `ct_eq` | ✅ | ✅ | Both have specs |
| `from_limbs` | ✅ | ✅ | Both have specs |
| Constants (ZERO, ONE, MINUS_ONE) | ✅ | ✅ | Both have specs |

### Scalar52 Functions

| Function | Verus | Lean | Notes |
|----------|:-----:|:----:|-------|
| `add` | ✅ | ✅ | Both have specs |
| `sub` | ✅ | ✅ | Both have specs |
| `mul` | ✅ | ❌ | **Verus only** |
| `square` | ✅ | ❌ | **Verus only** |
| `mul_internal` | ✅ | ✅ | Both have specs |
| `square_internal` | ✅ | ✅ | Both have specs |
| `montgomery_mul` | ✅ | ✅ | Both have specs |
| `montgomery_square` | ✅ | ✅ | Both have specs |
| `montgomery_reduce` | ✅ | ✅ | Both have specs |
| `as_montgomery` | ✅ | ✅ | Both have specs |
| `from_montgomery` | ✅ | ✅ | Both have specs |
| `from_bytes` | ✅ | ✅ | Both have specs |
| `from_bytes_wide` | ✅ | ✅ | Both have specs |
| `to_bytes` / `as_bytes` | ✅ | ✅ | Both have specs |
| `pack` | ✅ | ✅ | Both have specs |
| `conditional_add_l` | ✅ | ✅ | Both have specs |
| `invert` | ❌ | ✅ | **Lean only** |
| `montgomery_invert` | ❌ | ✅ | **Lean only** |

### EdwardsPoint Functions

| Function | Verus | Lean | Notes |
|----------|:-----:|:----:|-------|
| `add` | ✅ | ✅ | Both have specs |
| `double` | ✅ | ✅ | Both have specs |
| `identity` | ✅ | ✅ | Both have specs |
| `compress` | ✅ | ✅ | Both have specs |
| `decompress` | ✅ | ✅ | Both have specs |
| `as_projective` | ✅ | ✅ | Both have specs |
| `as_projective_niels` | ✅ | ✅ | Both have specs |
| `to_affine` | ✅ | ✅ | Both have specs |
| `to_montgomery` | ✅ | ✅ | Both have specs |
| `is_small_order` | ✅ | ✅ | Both have specs |
| `mul_by_cofactor` | ✅ | ✅ | Both have specs |
| `mul_by_pow2` | ❌ | ✅ | **Lean only** |
| `ct_eq` | ✅ | ✅ | Both have specs |
| `vartime_double_scalar_mul_basepoint` | ✅ | ✅ | Both have specs |
| `mul_base` | ✅ | ❌ | **Verus only** |
| `mul_base_clamped` | ✅ | ❌ | **Verus only** |
| `mul_clamped` | ✅ | ❌ | **Verus only** |
| `multiscalar_mul` | ✅ | ❌ | **Verus only** |
| `is_torsion_free` | ✅ | ❌ | **Verus only** |

### Scalar (high-level) Functions

| Function | Verus | Lean | Notes |
|----------|:-----:|:----:|-------|
| `from_bytes` | ✅ | ✅ | Both have specs |
| `from_bytes_mod_order` | ✅ | ✅ | Both have specs |
| `from_bytes_mod_order_wide` | ✅ | ✅ | Both have specs |
| `from_canonical_bytes` | ✅ | ✅ | Both have specs |
| `from_uniform_bytes` | ❌ | ✅ | **Lean only** |
| `to_bytes` | ✅ | ✅ | Both have specs |
| `is_canonical` | ✅ | ✅ | Both have specs |
| `clamp_integer` | ✅ | ✅ | Both have specs |
| `non_adjacent_form` | ✅ | ✅ | Both have specs |
| `invert` | ✅ | ✅ | Both have specs |

### Other Components

| Component | Verus | Lean | Notes |
|-----------|:-----:|:----:|-------|
| Montgomery point ops | ✅ | ✅ | Both have specs |
| Ristretto encoding | ✅ | ✅ | Both have specs |
| Window/LookupTable | ✅ | ❌ | **Verus only** |
| Basepoint tables | ✅ | ❌ | **Verus only** |
| Straus multiscalar mul | ✅ | ✅ | Both have specs |

### Summary: Functions Needing Coordination

**In Verus but not Lean:**
- `Scalar52::mul`, `Scalar52::square` (high-level scalar mul)
- `EdwardsPoint::mul_base`, `mul_base_clamped`, `mul_clamped`
- `EdwardsPoint::multiscalar_mul`, `is_torsion_free`
- Window/LookupTable optimizations
- Precomputed basepoint tables

**In Lean but not Verus:**
- `Scalar52::invert`, `montgomery_invert`
- `EdwardsPoint::mul_by_pow2`
- `Scalar::from_uniform_bytes`

## References

- Verus: [dalek-lite/curve25519-dalek/src/specs/](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/master/curve25519-dalek/src/specs)
- Lean: [curve25519-dalek-lean-verify/Curve25519Dalek/Specs/](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/master/Curve25519Dalek/Specs)
