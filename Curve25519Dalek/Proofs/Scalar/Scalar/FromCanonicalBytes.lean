/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `Scalar::from_canonical_bytes`

Specification and proof for `Scalar::from_canonical_bytes`.

This function constructs a scalar from canonical bytes.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input array b of type [u8;32].

      The condition checked is whether the Scalar s = Scalar{b} corresponding to the input array
      fulfils s.is_canonical(), which means that the number represented by b lies in [0, \ell - 1].

      If this condition is true, then the Scalar s is returned,
      otherwise None is returned.

      Note: Likely for efficiency reasons, the implementation also checks whether the most significant bit
      (bit with index 255) is 0, but this is redundant since any canonical scalar (< L ≈ 2^252) automatically has
      bits 253-255 equal to 0.

natural language specs:

    • If u8x32_to_nat(b) < \ell \then s = Scalar{b} else s = None
-/

/-- **Spec and proof concerning `scalar.Scalar.from_canonical_bytes`**:
- No panic (always returns successfully)
- When the input bytes represent a canonical value (< L), the function returns a CtOption Scalar
  where is_some = Choice.one and the scalar's byte representation equals the input bytes
- When the input bytes represent a non-canonical value (≥ L), the function returns a CtOption Scalar
  where is_some = Choice.zero (i.e., None)
-/
theorem from_canonical_bytes_spec (b : Array U8 32#usize):
    ∃ s,
    from_canonical_bytes b = ok s ∧
    (U8x32_as_Nat b < L → s.is_some = Choice.one ∧ s.value.bytes = b) ∧
    (U8x32_as_Nat b ≥ L → s.is_some = Choice.zero)
    := by
  sorry

end curve25519_dalek.scalar.Scalar
