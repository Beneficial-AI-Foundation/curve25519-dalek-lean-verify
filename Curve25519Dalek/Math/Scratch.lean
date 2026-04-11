import Curve25519Dalek.Math.BitList_B

open Aeneas Aeneas.Std BitList List

-- Test the strategy: apply bridge, then all_goals simp
-- Just test that the byte goals close automatically

-- Dummy bridge that takes 3 byte extract equalities
private theorem mini_bridge (x : U64) (b0 b1 b2 : U8)
    (hb0 : ofU8 b0 = (ofU64 x).extract 0 8)
    (hb1 : ofU8 b1 = (ofU64 x).extract 8 16)
    (hb2 : ofU8 b2 = (ofU64 x).extract 16 24) :
    True := trivial

example (x : U64) (shr0 shr1 shr2 : U64)
    (b0 b1 b2 : U8)
    (h_s0 : shr0.val = x.val >>> 0)
    (h_s1 : shr1.val = x.val >>> 8)
    (h_s2 : shr2.val = x.val >>> 16)
    (h_b0 : b0 = UScalar.cast .U8 shr0)
    (h_b1 : b1 = UScalar.cast .U8 shr1)
    (h_b2 : b2 = UScalar.cast .U8 shr2) :
    True := by
  -- Step 1: apply bridge, leaving 3 goals
  apply mini_bridge x b0 b1 b2
  -- Step 2: one line closes ALL 3 goals
  all_goals (
    subst_vars
    simp (discharger := omega) only [
      ofU8, ofU64, UScalar.cast_val_eq,
      UScalarTy.U8_numBits_eq,
      Nat.shiftRight_eq_div_pow,
      ofNat8_div_mod_eq_extract, *])
