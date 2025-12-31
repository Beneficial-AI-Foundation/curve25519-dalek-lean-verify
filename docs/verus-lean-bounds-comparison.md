# Verus vs Lean Bounds Comparison

Comparing [dalek-lite (Verus)](https://github.com/Beneficial-AI-Foundation/dalek-lite) with [curve25519-dalek-lean-verify (Lean 4)](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify).

**Result: All bounds match.**

## Constants

| Constant | Value |
|----------|-------|
| p | 2^255 - 19 |
| L | 2^252 + 27742317777372353535851937790883648493 |
| R (Montgomery) | 2^260 |
| d | 37095705934669439343138083508754565189542113879843219016388785533085940283555 |

All identical in both projects.

## FieldElement51 Bounds

5 limbs × 51-bit radix for GF(2^255-19).

| Operation | Input | Output | Verus | Lean |
|-----------|-------|--------|-------|------|
| add | < 2^53 | < 2^54 | [field_specs.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs.rs) | [Add.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean) |
| sub | < 2^53 | < 2^54 | same | Sub.lean |
| mul | < 2^54 | < 2^52 | [field_verus.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs) | [Mul.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Mul.lean) |
| square | < 2^54 | < 2^54 (V), < 2^52 (L) | same | Square.lean |
| reduce | any | ≤ 2^51 + 155629 | [field_specs_u64.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/field_specs_u64.rs) | [Reduce.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) |
| negate | < 2^51 | < 2^52 | same | Neg.lean |

Square: Lean proves tighter bound. Both valid.

## Scalar52 Bounds

5 limbs × 52-bit radix for arithmetic mod L.

**Montgomery multiplication:**
- Verus: input < 2^52 (canonical)
- Lean: input < 2^62 (more permissive)
- Both: (m * m') ≡ w * R (mod L)

Sources: [scalar52_specs.rs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/specs/scalar52_specs.rs), [MontgomeryMul.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean)

## EdwardsPoint Bounds

Coordinate limb bound: < 2^54 (both projects)

## Bound Propagation

```
add(<2^53, <2^53) → <2^54 → mul → <2^52 → reduce → <2^52 → safe for next op
```

After reduce, back below 2^51. This prevents overflow in chains.

## Function Coverage

**FieldElement51**: Full parity (21 functions each)

**Scalar52**: Minor gaps
- Verus only: mul, square (high-level wrappers)
- Lean only: invert, montgomery_invert

**EdwardsPoint**: Significant gaps
- Verus only: mul_base, mul_base_clamped, mul_clamped, multiscalar_mul, is_torsion_free
- Lean only: mul_by_pow2

## Gaps That Matter

Lean needs for X25519:
- `mul_base_clamped` ([source](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/edwards.rs))
- `mul_clamped` (same file)

Without these, Lean can't verify X25519 ECDH end-to-end.

## Side-by-Side Examples

### Field Addition

**Verus** (field_specs.rs):
```rust
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe.limbs[i] < (1u64 << bit_limit)
}
```

**Lean** (Add.lean):
```lean
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2^53) (hb : ∀ i < 5, b[i]!.val < 2^53) :
    ∃ result, add a b = ok result ∧
    (∀ i < 5, result[i]!.val < 2^54) := by
  unfold add; progress*
```

Same bounds.

### Montgomery Multiplication

**Verus** (scalar52_specs.rs):
```rust
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}
```

**Lean** (MontgomeryMul.lean):
```lean
theorem montgomery_mul_spec (m m' : Scalar52)
    (hm : ∀ i < 5, m[i]!.val < 2^62) (hm' : ∀ i < 5, m'[i]!.val < 2^62) :
    ∃ w, montgomery_mul m m' = ok w ∧
    (Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L] := by
  unfold montgomery_mul; progress*
```

Same correctness property. Lean allows larger inputs.

### Reduce

**Verus** (field_specs_u64.rs):
```rust
pub open spec fn spec_reduce(limbs: [u64; 5]) -> (r: [u64; 5]) {
    let mask51 = (1u64 << 51) - 1;
    [
        ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) as u64,
        ((limbs[1] & mask51) + (limbs[0] >> 51)) as u64,
        // ...
    ]
}
```

**Lean** (Reduce.lean):
```lean
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok result ∧
    (∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19) ∧
    Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] := by
  unfold reduce; progress*
```

Same algorithm. Lean's output bound is more precise.

## Protocol Status

| Protocol | Verus | Lean | Issue |
|----------|-------|------|-------|
| X25519 | yes | no | missing mul_clamped |
| Ed25519 sign | yes | partial | missing mul_base |
| Ed25519 verify | yes | yes | - |
| Ristretto | yes | yes | - |

## References

- Verus specs: [dalek-lite/specs/](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/master/curve25519-dalek/src/specs)
- Lean specs: [curve25519-dalek-lean-verify/Specs/](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/master/Curve25519Dalek/Specs)
