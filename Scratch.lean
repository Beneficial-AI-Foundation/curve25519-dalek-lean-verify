import Mathlib

attribute [grind =] Nat.add_mod Nat.mul_mod_mul_left Nat.mod_eq_of_lt
attribute [grind .] Nat.mod_lt

example (m n : Nat) (hn : 0 < n) :
    (1 + 2 * m) % (2 * n) = 1 + 2 * (m % n) := by
    grind 
