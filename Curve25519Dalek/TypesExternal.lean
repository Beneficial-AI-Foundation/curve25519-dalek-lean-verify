-- [curve25519_dalek]: external types.
import Aeneas
open Aeneas.Std Result

/- [subtle::Choice]
   Name pattern: [subtle::Choice]
   A constant-time boolean represented as 0 or 1 -/
structure subtle.Choice where
  val : U8
  valid : val = 0#u8 ∨ val = 1#u8
