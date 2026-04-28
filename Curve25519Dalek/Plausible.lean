-- Plausible property-based testing support for curve25519-dalek types.
--
-- Key findings from Aeneas source (used to guide instances below):
--   Std.U64  = UScalar .U64 = { bv : BitVec 64 }
--   Std.Array T n = { l : List T // l.length = n.val }
--   Construction: ⟨BitVec.ofNat 64 m⟩ for scalar types;
--                 Array.make / Array.repeat for array types.
--   WP.spec x p = theta x p, where theta dispatches on ok / fail / div.

import Plausible
import Curve25519Dalek.Funs

open Plausible Arbitrary
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

/-! ## Primitive scalar types

`Std.U8/U16/U32/U64/USize` are all `UScalar ty = { bv : BitVec ty.numBits }`.
`BitVec.ofNat` wraps any `Nat` via modulo, so no bounds proof is needed at the
call site — values from `Gen.choose` are already in range.
`Nat.shrink` halves toward 0, giving a proper shrink sequence (not just `[]`). -/

private def mkUScalar {ty : UScalarTy} (m : Nat) : UScalar ty :=
  { bv := BitVec.ofNat _ m }

-- Generate a UScalar with edge-case bias toward 0 and the max value.
private def genUScalarN (ty : UScalarTy) : Gen (UScalar ty) := do
  let max := 2 ^ ty.numBits - 1
  let rand := do let ⟨v, _⟩ ← Gen.choose Nat 0 max (Nat.zero_le _); pure v
  let m ← Gen.frequency rand [(90, rand), (5, pure 0), (5, pure max)]
  return mkUScalar m

instance : Arbitrary Std.U8    where arbitrary := genUScalarN .U8
instance : Arbitrary Std.U16   where arbitrary := genUScalarN .U16
instance : Arbitrary Std.U32   where arbitrary := genUScalarN .U32
instance : Arbitrary Std.U64   where arbitrary := genUScalarN .U64
instance : Arbitrary Std.Usize where arbitrary := genUScalarN .Usize

-- Shrink by halving the underlying Nat toward 0, then re-wrapping.
instance : Shrinkable Std.U8    where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U16   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U32   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U64   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.Usize where shrink u := Nat.shrink u.val |>.map mkUScalar
