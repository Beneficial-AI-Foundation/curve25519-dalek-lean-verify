/-
Legendre symbol checks for Elligator s1² ≠ -1 proof.
Verify via: lake env lean MWE_legendre.lean
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import PrimeCert.PrimeList

def my_p : Nat := 2^255 - 19
def my_d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

instance : Fact (Nat.Prime my_p) := ⟨PrimeCert.prime_25519''⟩

-- Q1: 1+d IS a square mod p (legendreSym = 1)
lemma one_plus_d_is_square : legendreSym my_p (1 + (my_d : ℤ)) = 1 := by
  norm_num [my_d, my_p]

-- Q2: -(d³-d-1) is NOT a square (Case A discriminant)
-- Quadratic: -(d²+d+1)r² - 2(1+d)r - d = 0, discriminant Δ_A = -4(d³-d-1)
lemma disc_A_not_square : legendreSym my_p (-((my_d : ℤ)^3 - (my_d : ℤ) - 1)) = -1 := by
  norm_num [my_d, my_p]

-- Q3: d(d+1) is NOT a square (Case B discriminant factor)
-- Quadratic: (1-d-d²)r² - 2d²r - d = 0, discriminant Δ_B = 4d(d-1)²(d+1)
-- Since 4(d-1)² is a perfect square, Δ_B is a square iff d(d+1) is a square.
lemma disc_B_not_square : legendreSym my_p ((my_d : ℤ) * (1 + (my_d : ℤ))) = -1 := by
  norm_num [my_d, my_p]
