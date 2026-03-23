# TODO: Proving `to_bytes_spec`

## Current state

- Bridge theorem `scalar52_eq_of_bitList_limbs` is proved (commented out while experimenting).
- Helper theorem `ofU8_val_eq_ofU64_drop_take` is proved.
- **Byte 0 proof is complete** — demonstrates the full proof chain.
- The 5 `hlimb` haves are still `sorry`'d. Main `to_bytes_spec` uses `sorry`.

## What we learned from byte 0

### Proof structure (3 phases)

**Phase 1: Resolve `result[j]!` through the 32-deep set chain**
```lean
subst_vars                                                    -- substitute all = postconditions
simp only [Array.getElem!_Nat_eq, Array.set_val_eq]          -- convert Array ops to List ops
simp_lists                                                    -- resolve (l.set i x)[j]! chain
```
- `subst_vars` eliminates ~70 variables (cast results, index results, array updates)
- `getElem!_set_ne` (`@[simp↓, simp_lists_simps↓]`) peels non-matching set layers
- `getElem!_set'` (`@[simp_lists_simps↓]`) resolves the matching set
- After this, `result[j]!` is resolved to `UScalar.cast .U8 i_shift` where `i_shift` is
  the shift result variable.

**Phase 2: Apply BitList helper**
```lean
conv_rhs => rw [show ... .take 8 = (... .drop k).take 8 from by simp]  -- if k=0
apply ofU8_val_eq_ofU64_drop_take _ _ k (by omega)
```
- Reduces to: `(UScalar.cast .U8 i_shift).val = self[limb].val / 2^k % 2^8`

**Phase 3: Close val-level goal using progress postconditions**
```lean
simp only [UScalar.cast, UScalar.val, BitVec.toNat_setWidth,
  UScalarTy.U8_numBits_eq, Nat.pow_zero, Nat.div_one]
show i_shift.val % 2^8 = self[limb].val % 2^8
rw [i_shift_post1, Nat.shiftRight_...]
have hlen : (↑self : List U64).length = 5 := self.property
simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
  hlen, Nat.reduceLT]
congr 1
```
- Unfolds `UScalar.cast` to get `i_shift.bv.toNat % 2^8`
- Uses `show` to convert `.bv.toNat` back to `.val` (definitionally equal)
- Uses shift postcondition `i_shift_post1` + `Nat.shiftRight_k`
- Normalizes `(↑self)[limb]!` to `self[limb]` via `getElem!_eq_getElem?_getD`
- Closes with `congr 1` (List vs Array GetElem proof irrelevance)

### Key issues discovered
1. **`UScalar.val` ↔ `.bv.toNat` loop**: Never use both `UScalar.val` and `i_post` in same simp.
   Instead, unfold val first, then `show` to convert back, then `rw [i_post]`.
2. **`UScalarTy.U8_numBits_eq`**: Needed to reduce `UScalarTy.U8.numBits` to `8`.
3. **getElem! vs getElem**: Progress gives `(↑self)[i]!` (bang), goal has `self[i]` (non-bang).
   Must normalize with `getElem!_eq_getElem?_getD` + length fact.
4. **Array vs List GetElem**: After normalization, `(↑self)[0]` (List) vs `self[0]` (Array)
   differ by irrelevant proof terms. `congr 1` closes this.

## Next steps

### Simple bytes (26 of 32)
The same pattern works for all bytes that are just `(self[limb] >>> k) as u8`:
- Bytes 0–5 from limb 0 (shifts 0, 8, 16, 24, 32, 40)
- Bytes 7–12 from limb 1 (shifts 4, 12, 20, 28, 36, 44)
- Bytes 13–18 from limb 2 (shifts 0, 8, 16, 24, 32, 40)
- Bytes 20–25 from limb 3 (shifts 4, 12, 20, 28, 36, 44)
- Bytes 26–31 from limb 4 (shifts 0, 8, 16, 24, 32, 40)

Only difference per byte: which `i_shift_post1` and which shift amount `k`.

### Shared bytes (2 of 32)
Bytes 6 and 19 involve `((limb_a >>> 48) | (limb_b <<< 4)) as u8`.
Need additional helper for OR + shift-left pattern.

### Architecture decision needed
1. **32 byte-level statements → hlimb statements**: Each hlimb is a concatenation of ~7 byte
   statements. Proving hlimb from byte statements should be straightforward with `simp` on
   BitList concat/take/drop lemmas.
2. **32 byte-level statements → bridge directly**: Rewrite the bridge theorem to accept 32
   byte facts instead of 5 hlimb facts. Might be cleaner and avoid the hlimb layer entirely.
3. **Keep current architecture**: Use byte-level proofs only as intermediate steps inside each
   hlimb proof. Might be cleanest overall.

### Potential improvements
- Extract Phase 3 into a reusable tactic/helper that takes the shift postcondition name and
  limb index, to reduce boilerplate across 30 nearly-identical byte proofs.
- The `conv_rhs` hack for `drop 0 = id` could be avoided by writing a version of the helper
  that doesn't require the `drop k` form (just takes `k` as a Nat for the division).
