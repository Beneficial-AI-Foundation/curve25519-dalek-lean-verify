# Verus vs Lean Bounds

[Verus](https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/master/curve25519-dalek/src/specs) · [Lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/master/Curve25519Dalek/Specs)

## Lean exports tighter bounds

| Op | Verus exports | Lean exports | Ratio |
|----|---------------|--------------|-------|
| square | < 2⁵⁴ | < 2⁵² | 4× |
| reduce | < 2⁵² | ≤ 2⁵¹+155k | 2× |

**Key insight**: Verus *internally* proves tighter bounds but rounds up for simpler API:

```rust
// reduce_lemmas.rs:47-60 - Verus knows:
limb 0: < 2^51 + 2^18  (= 2^51 + 262144)
limbs 1-4: < 2^51 + 2^13  (= 2^51 + 8192)
// But exports: < 2^52 for all
```

Lean exports the tighter bound directly: `≤ 2^51 + 155629` (tighter than Verus's internal 2^51 + 262144).

**Could Verus match Lean?** Yes - it's a design choice, not a capability limit. Verus could:
1. Export per-limb bounds (limb 0 vs limbs 1-4)
2. Use `(2^13 - 1) * 19 = 155629` instead of `2^18 = 262144`

**Further tightening possible** (neither project does yet):
- reduce limbs 1-4: `≤ 2^51 + 8191` (no `*19` factor)
- square: Pow2K.lean:208 claims `< 2^51` achievable

## FieldElement51 (5×51-bit limbs, GF(2²⁵⁵-19))

| Op | In | Verus Out | Lean Out | Tighter |
|----|---:|----------:|---------:|:-------:|
| add | 2⁵³ | 2⁵⁴ | 2⁵⁴ | = |
| mul | 2⁵⁴ | 2⁵² | 2⁵² | = |
| square | 2⁵⁴ | 2⁵⁴ | 2⁵² | **L** |
| reduce | ∞ | 2⁵² | 2⁵¹+155k | **L** |

Sources: [V:field_verus.rs#L163](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L163) [V:pow2k#L468](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L468) [L:Square.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square.lean#L39) [L:Reduce.lean](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean#L50)

### Why Lean is tighter

**square**: Verus proves output < 2⁵⁴ via `pow2k` loop invariant. Lean proves < 2⁵² directly for k=1.

**reduce**: Verus proves `< 2^52`. Lean proves the precise bound `≤ 2^51 + (2^13-1)*19 = 2^51 + 155629`. Since 2⁵¹+155629 ≈ 2⁵¹·⁰⁰⁰¹ < 2⁵², Lean's bound is ~2× tighter.

## Scalar52 (5×52-bit limbs, mod L)

Montgomery mul: V requires 2⁵², L allows 2⁶². Both: `m·m' ≡ w·R (mod L)`.

## Gaps

| | Verus only | Lean only |
|-|------------|-----------|
| Scalar52 | mul, square | invert |
| Edwards | mul_base, mul_clamped | mul_by_pow2 |

**X25519 blocked**: Lean missing [mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/master/curve25519-dalek/src/edwards.rs#L500)

## Evidence

**Verus pow2k** (used by square):
```rust
// field_verus.rs#L468-L475
pub fn pow2k(&self, mut k: u32) -> (r: FieldElement51)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54,
    ensures
        forall|i: int| 0 <= i < 5 ==> r.limbs[i] < 1u64 << 54,  // output bound
```

**Lean square**:
```lean
-- Square.lean#L39-L41
theorem square_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, square a = ok r ∧ ... ∧ (∀ i < 5, r[i]!.val < 2 ^ 52)  -- tighter!
```

**Verus reduce**:
```rust
// field_verus.rs#L163-L166
fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)
    ensures
        forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
```

**Lean reduce**:
```lean
-- Reduce.lean#L50-L52
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok result ∧
    (∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19)  -- tighter!
```
