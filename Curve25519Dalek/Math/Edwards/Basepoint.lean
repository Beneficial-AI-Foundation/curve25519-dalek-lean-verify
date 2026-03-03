/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Edwards.Curve

/-! # Ed25519 Basepoint Order

The Ed25519 basepoint B = (x, y) has prime order L in the Edwards curve group.
This is a purely mathematical fact, independent of any implementation representation.

The basepoint coordinates are the standard Ed25519 values:
- y = 4/5 mod p (the canonical generator y-coordinate)
- x is the positive square root derived from the curve equation
-/

namespace Edwards

private def basepoint : Point Ed25519 where
  x := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  y := 46316835694926478169428394003475163141307993866256225615783033603165251855960
  on_curve := by decide

/-- The Ed25519 basepoint has order L, i.e., L • basepoint = 0.

This is verified computationally using double-and-add scalar multiplication via `native_decide`. -/
theorem basepoint_order_L :
    L • basepoint = 0 := by
  rw [(binary_nsmul_Ed25519_eq L basepoint).symm]
  native_decide

end Edwards
