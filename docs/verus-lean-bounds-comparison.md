# Verus vs Lean Bounds

[Verus](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/master/curve25519-dalek/src/specs) · [Lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/master/Curve25519Dalek/Specs)

## FieldElement51 (5×51-bit limbs, GF(2²⁵⁵-19))

| Op | In | Out | Sources |
|----|---:|----:|---------|
| add | 2⁵³ | 2⁵⁴ | [V](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs.rs#L27) [L](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean#L24) |
| mul | 2⁵⁴ | 2⁵² | [V](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs) [L](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Mul.lean) |
| square | 2⁵⁴ | 2⁵⁴/2⁵² | [V](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs) [L](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square.lean) |
| reduce | ∞ | 2⁵¹+155k | [V](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs_u64.rs#L62) [L](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean#L50) |

## Scalar52 (5×52-bit limbs, mod L)

Montgomery mul: V requires 2⁵², L allows 2⁶². Both: `m·m' ≡ w·R (mod L)`.
[V](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/scalar52_specs.rs#L69) [L](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean#L41)

## Gaps

| | Verus only | Lean only |
|-|------------|-----------|
| Scalar52 | mul, square | invert |
| Edwards | mul_base, mul_clamped | mul_by_pow2 |

**X25519 blocked**: Lean missing [mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/edwards.rs#L500)

## Side-by-side

**add**
```rust
// Verus: field_specs.rs
forall|i: int| 0 <= i < 5 ==> fe.limbs[i] < (1u64 << bit_limit)
```
```lean
-- Lean: Add.lean
∀ i < 5, a[i]!.val < 2^53 → ∀ i < 5, result[i]!.val < 2^54
```

**reduce**
```rust
// Verus: field_specs_u64.rs
((limbs[0] & mask51) + (limbs[4] >> 51) * 19) as u64  // limb 0
((limbs[k] & mask51) + (limbs[k-1] >> 51)) as u64     // limbs 1-4
```
```lean
-- Lean: Reduce.lean
∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19
```
