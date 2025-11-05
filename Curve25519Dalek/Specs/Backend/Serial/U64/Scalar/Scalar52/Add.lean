/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
import Curve25519Dalek.Aux

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000

/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (u u' : Scalar52) :
    ∃ v,
    add u u' = ok v ∧
    Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L
    := by
  unfold add
  progress*
  -- After progress*, we have expanded the initial computations (mask creation)
  -- The remaining proof requires:
  -- 1. Showing add_loop succeeds and computes sum = u + u' (modulo carry handling)
  -- 2. Showing sub sum L succeeds and produces v such that v ≡ (u + u') mod L
  -- 3. Showing v < L (canonical form)
  -- This depends on sub_spec being complete, which is currently incomplete
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
