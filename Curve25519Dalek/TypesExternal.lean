/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
open Aeneas.Std Result

/-!
# External type definitions for `curve25519_dalek`

Manual Lean definitions for types from external crates (`core`, `subtle`)
whose definitions cannot be extracted by Aeneas but are referenced by the
extracted `curve25519-dalek` code.
-/

namespace curve25519_dalek

/- [core::fmt::Arguments]
   Name pattern: [core::fmt::Arguments] -/
axiom core.fmt.Arguments : Type

/- [subtle::Choice]
   Name pattern: [subtle::Choice]
   A constant-time boolean represented as 0 or 1 -/
structure subtle.Choice where
  val : U8
  valid : val = 0#u8 ∨ val = 1#u8

/- [subtle::CtOption]
   Name pattern: [subtle::CtOption]
   A constant-time optional type -/
structure subtle.CtOption (T : Type) where
  value : T
  is_some : subtle.Choice

end curve25519_dalek
