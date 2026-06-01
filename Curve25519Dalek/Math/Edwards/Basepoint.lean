/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Edwards.Curve
-- Scalar multiplication over the large-prime field is infeasible for kernel `decide`;
-- `native_decide` is used instead.
set_option linter.style.nativeDecide false

/-! # Ed25519 Basepoint Order

This file contains the purely mathematical facts related to the ed25519 basepoint, independent of
any implementation representation.

Key results:
- `basepoint ≠ 0`
- `4 • basepoint ≠ 0`
- `L • basepoint = 0`
-/

namespace Edwards

def basepoint : Point Ed25519 where
  x := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  y := 46316835694926478169428394003475163141307993866256225615783033603165251855960
  on_curve := by decide

/-- The Ed25519 basepoint has order L, i.e., L • basepoint = 0.

This is verified computationally using double-and-add scalar multiplication via `native_decide`. -/
theorem basepoint_order_L : L • basepoint = 0 := by
  rw [← binary_nsmul_Ed25519_eq L basepoint]
  native_decide

theorem basepoint_ne_zero : basepoint ≠ 0 := by decide

theorem four_nsmul_basepoint_ne_zero : 4 • basepoint ≠ 0 := by native_decide

end Edwards
