-- [curve25519_dalek]: external types.
import Aeneas
open Aeneas.Std Result
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
