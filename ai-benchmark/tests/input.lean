/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub_loop`**: -/
@[progress]
theorem sub_loop_spec (mask : U64) (a b difference : Array U64 5#usize) (borrow : U64) (i : Usize)
    (ha : ∀ j, j < 5 → (a[j]!).val < 2 ^ 52) (hb : ∀ j, j < 5 → (b[j]!).val < 2 ^ 52)
    (hd : ∀ j, j < i.val → difference[j]!.val < 2 ^ 52)
    (hd_rest : ∀ j, i.val ≤ j → j < 5 → difference[j]!.val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hborrow : borrow.val.testBit 63 = false ∨ borrow.val.testBit 63 = true) :
    ∃ difference' borrow', sub_loop mask a b difference borrow i = ok (difference', borrow') ∧
    U64x5_slice_as_Nat a i + 2 ^ (52 * i.val) * (if borrow.val.testBit 63 then 1 else 0) =
      U64x5_slice_as_Nat b i + U64x5_slice_as_Nat difference' i +
      2 ^ (52 * 5) * (if borrow'.val.testBit 63 then 1 else 0) ∧
    (∀ j, j < 5 → difference'[j]!.val < 2 ^ 52)
  := by
  unfold sub_loop
  unfold backend.serial.u64.scalar.Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  unfold backend.serial.u64.scalar.IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  split
  · progress*
    · sorry
    · sorry
    · sorry
    · sorry
  · use difference, borrow
    constructor
    · rfl
    · constructor
      · simp [U64x5_slice_as_Nat]
        have : i.val = 5 := by scalar_tac
        simp [this]
        -- When we've processed all 5 limbs, the arithmetic property should hold
        sorry
      · intro j hj
        by_cases h : j < i.val
        · exact hd j h
        · have : i.val ≤ j := by omega
          have hz := hd_rest j this hj
          omega
  termination_by 5 - i.val
  decreasing_by scalar_decr_tac

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub`**:
- Does not error and hence returns a result
- The result represents (a - b) mod L where L is the group order
- Requires that input limbs are within bounds (52-bit values) -/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52) :
    ∃ result, sub a b = ok result ∧
    Scalar52_as_Nat result ≡ (Scalar52_as_Nat a - Scalar52_as_Nat b) [MOD L] := by
  unfold sub
  -- progress*

  sorry
