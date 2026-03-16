import Curve25519Dalek.Funs

open Aeneas Aeneas.Std

-- Direct approach: unfold both sides manually
example (self : Array U64 5#usize) : self[0]! = self[0] := by
  have hlen : self.val.length = 5 := self.property
  -- Restore the simp lemma Aeneas removed
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, dite_true, Option.getD_some, hlen]

example (self : Array U64 5#usize) : self[0]! = self[0] := by
  have hlen : self.val.length = 5 := self.property
  show self.val[0]! = self.val[0]'(by omega)
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (h := by omega),
    Option.getD_some]
