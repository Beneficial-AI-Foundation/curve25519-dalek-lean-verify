/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Alessandro D'Angelo, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # `EdwardsPoint::vartime_double_scalar_mul_basepoint`

Computes `[a]A + [b]B` in variable time, where `B` is the Ed25519 basepoint.
Used by Ed25519 signature verification (the canonical caller is
`ristretto::RistrettoPoint::vartime_double_scalar_mul_basepoint`, which delegates here).

**Source**: `curve25519-dalek/src/edwards.rs:1037-1047`

## Status: cannot specify yet — function not extracted

The Rust impl is gated by `#[cfg(not(verify))]`:
```rust
#[cfg(not(verify))]
impl EdwardsPoint {
    pub fn vartime_double_scalar_mul_basepoint(
        a: &Scalar, A: &EdwardsPoint, b: &Scalar
    ) -> EdwardsPoint {
        crate::backend::vartime_double_base_mul(a, A, b)
    }
}
```

This means the `verify` cfg flag (set during Aeneas extraction) **excludes** this function
from `Funs.lean`. Consequently no `theorem ..._spec` of the form
`vartime_double_scalar_mul_basepoint ... ⦃ ... ⦄` can be written until either:
1. The cfg gating is removed upstream and `vartime_double_base_mul` (the inner backend call,
   itself a `TODO` stub at `Specs/Backend/VartimeDoubleBaseMul.lean`) becomes extractable, or
2. We add an external axiom mirror in `FunsExternal.lean` (analogous to other Aeneas-untranslatable
   pieces like dynamic dispatch and iterators).

The cfg gate is most likely there because `vartime_double_base_mul` dispatches to one of several
backends (serial / AVX2 / AVX512) via runtime backend selection, which Aeneas cannot translate.

## Target spec shape (for when extraction is unblocked)

The Verus port at `dalek-lite/curve25519-dalek/src/edwards.rs:2853-2869` specifies:
- **Pre**: `is_well_formed_edwards_point(*A) ∧ scalar_as_nat(a) < 2^255 ∧ scalar_as_nat(b) < 2^255`
- **Post**: `result.IsValid` ∧
  `result.toPoint = (U8x32_as_Nat a.bytes) • A.toPoint`
  ` + (U8x32_as_Nat b.bytes) • Edwards.basepoint`

Concretely, the future Lean theorem will read:
```
@[step, externally_verified] -- proven in Verus
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint)
    (b : scalar.Scalar) (h_A_valid : A.IsValid)
    (h_a_canonical : U8x32_as_Nat a.bytes < 2 ^ 255)
    (h_b_canonical : U8x32_as_Nat b.bytes < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ result =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat a.bytes) • A.toPoint
                       + (U8x32_as_Nat b.bytes) • _root_.Edwards.basepoint ⦄ := by
  sorry
```

-/

-- No Lean specification possible until extraction is unblocked.
