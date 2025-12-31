# Verus vs Lean Bounds

[Verus](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/master/curve25519-dalek/src/specs) · [Lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/master/Curve25519Dalek/Specs)

## FieldElement51

| Op | In | Verus Out | Lean Out |
|----|---:|----------:|---------:|
| add | 2⁵³ | 2⁵⁴ | 2⁵⁴ |
| mul | 2⁵⁴ | 2⁵² | 2⁵² |
| square | 2⁵⁴ | 2⁵⁴ | 2⁵² |
| reduce | ∞ | 2⁵² | 2⁵¹+155k |

## Scalar52

| Op | Verus In | Lean In |
|----|----------|---------|
| montgomery_mul | 2⁵² | 2⁵² |

Tighter 2⁵¹+155k: proofs work, but RR constant limbs ∈ [2⁵¹+155k, 2⁵²). Not recommended.

## Gaps

| | Verus only | Lean only |
|-|------------|-----------|
| Scalar52 | mul, square | invert |
| Edwards | mul_base, mul_clamped | mul_by_pow2 |
