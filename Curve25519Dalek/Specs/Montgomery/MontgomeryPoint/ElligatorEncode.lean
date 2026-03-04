/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.MONTGOMERY_A
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.MONTGOMERY_A_NEG

/-! # Spec Theorem for `elligator_encode`

Specification and proof for `curve25519_dalek::montgomery::elligator_encode`.

This function performs the Elligator 2 map from a field element `r_0` to a
`(MontgomeryPoint, Choice)` pair. The map is a deterministic, surjective function
from field elements onto approximately half the Montgomery u-coordinates, and is
used by hash-to-curve algorithms (RFC 9380, §6.7.3).

**Source**: curve25519-dalek/src/montgomery.rs, lines 263:0-284:1

**Reference**: <https://www.rfc-editor.org/rfc/rfc9380.html#name-elligator-2-method>

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.montgomery

/-
Natural language description:

    The Elligator 2 map on the Montgomery curve y² = x³ + Ax² + x
    (where A = 486662 is MONTGOMERY_A):

    Given an input field element r₀:

    1.  Compute d₁ = 1 + 2·r₀²            (denominator of the candidate u)

    2.  Compute d  = −A · d₁⁻¹             (candidate u-coordinate; note
                  = −A/(1 + 2·r₀²))

    3.  Compute eps = d · (d² + A·d + 1)   (the value of the right-hand side
                                             of the Montgomery equation at u = d;
                                             i.e. eps = d³ + A·d² + d)

    4.  Determine whether eps is a quadratic residue (QR) mod p via
        `sqrt_ratio_i(eps, ONE)`.

    5.  Select the output u-coordinate:
        - If eps is a QR  → u := d            (then d  lies on the curve)
        - If eps is a NQR → u := −d − A       (then −d−A lies on the curve's twist;
                                               note u = −(d + A))

    6.  Return `(MontgomeryPoint(u.to_bytes()), eps_is_sq)`.

    The special case r₀ = 0 gives d₁ = 1, d = −A, eps = −A(A²−A+1).
    In that case eps = 0 (since 0 is a square), so u = d = −A maps to
    the point at infinity, which is the identity element.

Natural language specs:

    - The function always succeeds (never panics) for any field element input r₀.

    - The returned `Choice` (eps_is_sq) satisfies:
        eps_is_sq.val = 1#u8  ↔  eps is a quadratic residue mod p,
      where eps = d·(d² + A·d + 1) and d = −A/(1 + 2·r₀²) (mod p).

    - The returned `MontgomeryPoint` encodes the field element u (mod p):
        • If eps_is_sq = 1 (eps is a QR):   u ≡   d    (mod p)
        • If eps_is_sq = 0 (eps is a NQR):  u ≡ −d − A  (mod p)

    - In the QR case, u(u² + A·u + 1) is a perfect square mod p, so
      (u, v) lies on the Montgomery curve for some v.

    - In the NQR case, u(u² + A·u + 1) is a non-square mod p (i.e. u lies
      on the quadratic twist of the Montgomery curve).

    - The output u-coordinate always satisfies u ≠ −1 (mod p) whenever
      d₁ = 1 + 2·r₀² ≠ 0, so the birational map to Edwards coordinates
      is well-defined on u.

    - The computation is deterministic (no randomness) and suitable for
      hashing to the Montgomery curve in constant time.
-/

/- **Spec and proof concerning `montgomery.elligator_encode`**:
- No panic (always returns successfully) for any field element input
- Implements the Elligator 2 map following RFC 9380 §6.7.3 for Curve25519
- Mathematical properties of the result `(point, eps_is_sq)`:
  * Let A := 486662 (the Montgomery curve parameter, MONTGOMERY_A) as a field element in ZMod p
  * Let r  := r₀ as a field element in ZMod p  (i.e. (Field51_as_Nat r₀ : ZMod p))
  * Let d₁ := 1 + 2·r²  ∈ ZMod p              (denominator; note d₁ ≠ 0 since 2r² ≠ −1 mod p)
  * Let d  := −A · d₁⁻¹ ∈ ZMod p              (primary candidate u-coordinate)
  * Let eps := d · (d² + A·d + 1) ∈ ZMod p    (Montgomery RHS evaluated at u = d)
  * The returned Choice eps_is_sq satisfies:
      eps_is_sq.val = 1#u8 ↔ IsSquare (eps : ZMod p)
  * The returned MontgomeryPoint encodes the field element:
      u = if IsSquare eps then d else -d - A
  * Concretely, U8x32_as_Nat point % p equals
      (Field51_as_Nat d_field) % p             when eps is a QR, or
      (p - (Field51_as_Nat d_field + 486662) % p) % p  when eps is a NQR
  * When eps is a QR, u = d satisfies u·(u² + A·u + 1) ≡ eps (mod p), which is
    a square, so (u, v) lies on the Montgomery curve y² = x³ + Ax² + x
  * When eps is a NQR, u = −d − A satisfies u·(u² + A·u + 1) ≡ −eps·(some square) (mod p),
    so (u, v) lies on the quadratic twist of the Montgomery curve
  * The map is injective on each coset of the subgroup {±1}, i.e.
    elligator_encode(r₀) and elligator_encode(−r₀) give the same MontgomeryPoint
    (since r₀² = (−r₀)²)
  * The computation maintains constant-time guarantees: all branches are resolved
    via conditional-select and conditional-assign operations
-/

@[progress]
theorem elligator_encode_spec
    (r_0 : backend.serial.u64.field.FieldElement51)
    (h_bounds : ∀ i, i < 5 → (r_0[i]!).val ≤ 2 ^ 52 - 1) :
    elligator_encode r_0 ⦃ res =>
    -- Field arithmetic interpretation of input and outputs
    let r     : ZMod p := (Field51_as_Nat r_0 : ZMod p)
    let d_1   : ZMod p := 1 + 2 * r ^ 2
    let d     : ZMod p := -Curve25519.A * d_1⁻¹
    let eps   : ZMod p := d * (d ^ 2 + Curve25519.A * d + 1)
    let point  := res.1
    let eps_is_sq := res.2
    -- The returned Choice correctly identifies whether eps is a square
    (eps_is_sq.val = 1#u8 ↔ IsSquare eps) ∧
    -- The returned MontgomeryPoint encodes the Elligator 2 u-coordinate
    (eps_is_sq.val = 1#u8 →
      (U8x32_as_Nat point : ZMod p) = d) ∧
    (eps_is_sq.val = 0#u8 →
      (U8x32_as_Nat point : ZMod p) = -d - Curve25519.A) ∧
    -- In the QR case, u lies on the Montgomery curve
    (eps_is_sq.val = 1#u8 →
      let u : ZMod p := (U8x32_as_Nat point : ZMod p)
      u * (u ^ 2 + Curve25519.A * u + 1) = eps) ∧
    -- In the NQR case, u lies on the quadratic twist
    (eps_is_sq.val = 0#u8 →
      let u : ZMod p := (U8x32_as_Nat point : ZMod p)
      IsSquare (-(u * (u ^ 2 + Curve25519.A * u + 1)))) ⦄ := by
    sorry

end curve25519_dalek.montgomery
