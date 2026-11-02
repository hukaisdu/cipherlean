# DdtInverse — formalization of "Lemma (DDT of the inverse S-box)"

## Source
- No paper. The statement is the user's own, given in chat on 2026-11-01 and copied verbatim below; it is the only
  source for this formalization (no literature search was made, by instruction).
- Files: `Main.lean` (the lemma in three spellings, the matrix form, the finite checks), `CHAIN.md` + `CHAIN.pdf`
  (chain, graph, roadmap), `NOTATION.md` (every symbol and its Lean name). The encodings and the proof come from the
  shared library `CipherLean` (`Vec`, `ddt`, `ddt_symm`, `ddt_eq_ddt_of_inverse`, `image_cond`): migrated on
  2026-11-01, when the other spellings of the lemma were promoted into the library.

## Statement (verbatim)
> Lemma (DDT of the inverse S-box). Let S be a permutation of F_2^n and S^{-1} its inverse.
> For all a, b ∈ F_2^n:
>   #{x ∈ F_2^n : S(x ⊕ a) ⊕ S(x) = b} = #{y ∈ F_2^n : S^{-1}(y ⊕ b) ⊕ S^{-1}(y) = a}.
> In words: the DDT of S^{-1} is the transpose of the DDT of S.

## Hypotheses
Objects and their encodings are in `NOTATION.md`; the proof's steps are the rows of `CHAIN.md`.

| hypothesis | in the source | explicit or implicit | Lean |
|---|---|---|---|
| `S` is a permutation of `F_2^n` | "Let S be a permutation" | explicit | `S : Equiv.Perm (Vec ι)` (main); `hS : Function.Bijective S` (`ddt_invFun`) |
| `S^{-1}` is the inverse of `S` | "`S^{-1}` its inverse" | explicit (two equations in Lean) | `S.symm`; `Function.invFun S`; or `T` with `hTS : ∀ x, T (S x) = x`, `hST : ∀ y, S (T y) = y` |
| `a, b` arbitrary, zero allowed; `n` unbounded | "for all a, b", "`F_2^n`" | explicit | `(a b : Vec ι)`, any finite `ι` (`n = 0` allowed) |

Nothing is implicit, and the inverse hypothesis cannot be dropped (counterexamples below). One finding: on the
finite set `F_2^n` the two inverse equations are not independent — `T ∘ S = id` alone implies `S ∘ T = id`
(`ddt_eq_ddt_of_leftInverse`).

## Finite checks
- Toy: `toyS` (`Sbox.ofTable`, the 3-cycle `5 ↦ 6 ↦ 7 ↦ 5` on `BitVec 3`) with inverse `toyInv` (`toyInv_toyS`,
  `toyS_toyInv`); `toy_ddt_transpose` — the identity for all 64 pairs; `toy_values` — `ddt toyS 1 2 = 4`,
  `ddt toyS 2 1 = 0` and the inverse has them exchanged (numbers computed in Python beforehand).
- Counterexample for "`T` is the inverse of `S`": `toy_not_symmetric` (`T = S`) and `toy_id_fails` (`T = id`), both
  failing at `(a, b) = (1, 2)`. No counterexample exists for dropping only one of the two inverse equations on
  `Vec ι` (`ddt_eq_ddt_of_leftInverse`).

## Status
2026-11-01: `check_lean.py` VERDICT: PASS (14 declarations, standard axioms, no `native_decide`) ·
`chain_check.py` CONSISTENT · `notation_check.py` OK. `status.py DdtInverse` prints the live board.

| source label | Lean declaration | status | axioms | note |
|---|---|---|---|---|
| Lemma (DDT of the inverse S-box) | `DdtInverse.ddt_symm` (= `CipherLean.ddt_symm`) | proved | standard | `S : Equiv.Perm (Vec ι)`, `S^{-1} = S.symm`; the main theorem |
| same lemma, `S` a bijective function | `DdtInverse.ddt_invFun` (= `CipherLean.ddt_invFun`) | proved | standard | `S^{-1} = Function.invFun S` |
| same lemma, explicit inverse `T` (the engine) | `CipherLean.ddt_eq_ddt_of_inverse` (library) | proved | standard | hypotheses `T (S x) = x`, `S (T y) = y` |
| remark: one inverse equation suffices | `DdtInverse.ddt_eq_ddt_of_leftInverse` (= `CipherLean.ddt_eq_ddt_of_leftInverse`) | proved | standard | only `T (S x) = x` assumed |
| "In words": the transpose | `DdtInverse.ddtMatrix_symm` (= `CipherLean.ddtMatrix_symm`) | proved | standard | `ddtMatrix S.symm = (ddtMatrix S).transpose` |
| toy and counterexamples | `toy_ddt_transpose`, `toy_values`, `toyInv_toyS`, `toyS_toyInv`, `toy_not_symmetric`, `toy_id_fails` | proved (`decide` through `ddt_toFun`) | standard | |

`standard` = `propext`, `Classical.choice`, `Quot.sound`.

## Departures from the source
- `F_2^n` is the library carrier `Vec ι` for any finite index type `ι` (`ι = Fin n` recovers `n`-bit words); `n = 0`
  is allowed, where the lemma holds trivially. The source presumably has `n ≥ 1` in mind; no hypothesis was added.
- "`S` is a permutation" is `S : Equiv.Perm (Vec ι)` with `S^{-1} = S.symm` (main theorem); two further spellings are
  proved so that no reader has to convert: a bijective function with `Function.invFun`, and an explicit inverse `T`
  with the two equations as hypotheses (the engine).
- `ddt` is defined for every function `S`, not only permutations; bijectivity enters only through the inverse.
- The finite checks state the facts on `Vec (Fin 3)` and decide them on `BitVec 3` through `CipherLean.ddt_toFun`.
- The `y` of the source's second count is the bound variable `x` of `ddt`; nothing else is renamed.

## Roadmap
The plan is the Roadmap table of `CHAIN.md` (one piece, done); the position after the run:

### 2026-11-01 — after piece A (the whole lemma)
#### Position — DdtInverse (2026-11-01; regenerated 2026-11-03)
- End: self-contained — every row proved here with standard axioms; reached on 2026-11-01.
- Rows: 6 proved · 2 stated · 0 pending · 0 cited · 1 assumed (of 9)
- Pieces: 1 done of 1 (A); sessions 1 of ≈ 1 (size-weighted progress 100 %)
- Remaining: nothing — the end is reached

## Rebuild
```
cd ~/cipherlean && ~/.claude/skills/cipherlean/scripts/lake_build.sh CipherLean.Examples.DdtInverse.Main && ~/.claude/skills/cipherlean/scripts/check_lean.py CipherLean/Examples/DdtInverse/Main.lean --no-build && ~/.claude/skills/cipherlean/scripts/chain_check.py CipherLean/Examples/DdtInverse/CHAIN.md CipherLean/Examples/DdtInverse/Main.lean
```
