# ToMathlib

Results proved here are candidates for upstreaming to Mathlib. Each file includes a comment indicating where in Mathlib the result should live.

## Performance note

When working with `ZMod p` where `p` is a large literal (e.g., `p = 2^255 - 19`), always prove results in the most general form first (e.g., for an arbitrary finite field `F` with `ringChar F ≠ 2`), then specialize to the concrete case. Working directly with large numbers causes severe performance problems in Lean — the kernel and tactics struggle with big numeric literals in proof terms. Keeping proofs generic avoids this entirely.

Pattern:
1. Prove the general result: `theorem FiniteField.foo [Field F] [Finite F] ...`
2. Specialize at the use site: `FiniteField.foo ringChar_ne_two ...`
