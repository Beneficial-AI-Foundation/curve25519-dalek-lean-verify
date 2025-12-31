# Verus vs Lean Bounds Comparison

[dalek-lite (Verus)](https://github.com/Beneficial-AI-Foundation/dalek-lite) vs [curve25519-dalek-lean-verify (Lean)](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify)

All bounds match.

## FieldElement51

5 limbs × 51-bit radix for GF(2^255-19).

| Op | Input | Output | Verus | Lean |
|----|-------|--------|-------|------|
| add | < 2^53 | < 2^54 | [field_specs.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs.rs) | [Add.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean) |
| sub | < 2^53 | < 2^54 | same | Sub.lean |
| mul | < 2^54 | < 2^52 | [field_verus.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs) | [Mul.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Mul.lean) |
| square | < 2^54 | < 2^54 / < 2^52 | same | Square.lean |
| reduce | any | ≤ 2^51 + 155629 | [field_specs_u64.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs_u64.rs) | [Reduce.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) |
| negate | < 2^51 | < 2^52 | same | Neg.lean |

## Scalar52

5 limbs × 52-bit radix for arithmetic mod L.

Montgomery mul: Verus requires < 2^52, Lean allows < 2^62. Both prove `(m * m') ≡ w * R (mod L)`.

Sources: [scalar52_specs.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/scalar52_specs.rs), [MontgomeryMul.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean)

## EdwardsPoint

Coordinate limbs: < 2^54 (both)

## Function Gaps

| Component | Verus only | Lean only |
|-----------|------------|-----------|
| Scalar52 | mul, square | invert |
| EdwardsPoint | mul_base, mul_clamped, mul_base_clamped, multiscalar_mul | mul_by_pow2 |

Lean needs mul_clamped for X25519: [edwards.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/edwards.rs)

## Code Examples

### add (Verus)
```rust
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe.limbs[i] < (1u64 << bit_limit)
}
```

### add (Lean)
```lean
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2^53) (hb : ∀ i < 5, b[i]!.val < 2^53) :
    ∃ result, add a b = ok result ∧ (∀ i < 5, result[i]!.val < 2^54) := by
  unfold add; progress*
```

### reduce (Verus)
```rust
pub open spec fn spec_reduce(limbs: [u64; 5]) -> [u64; 5] {
    let mask51 = (1u64 << 51) - 1;
    [
        ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) as u64,
        ((limbs[1] & mask51) + (limbs[0] >> 51)) as u64,
        ((limbs[2] & mask51) + (limbs[1] >> 51)) as u64,
        ((limbs[3] & mask51) + (limbs[2] >> 51)) as u64,
        ((limbs[4] & mask51) + (limbs[3] >> 51)) as u64,
    ]
}
```

### reduce (Lean)
```lean
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok result ∧
    (∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19) ∧
    Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] := by
  unfold reduce; progress*
```

## Protocol Status

| Protocol | Verus | Lean |
|----------|-------|------|
| X25519 | yes | no (missing mul_clamped) |
| Ed25519 verify | yes | yes |
| Ristretto | yes | yes |
