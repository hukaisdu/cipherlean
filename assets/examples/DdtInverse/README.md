# DdtInverse — formalization of "Lemma (DDT of the inverse S-box)"

## Source
- No paper. The statement is the user's own, given in chat on 2026-11-01 and copied verbatim below;
  it is the only source for this formalization (no literature search was made, by instruction).
- Files: `Main.lean` (statements in the three spellings, matrix form, finite checks), `NOTATION.md`
  (symbol ↔ Lean name). Encodings and the proof come from the shared library `Formal.Crypto`
  (`Crypto.Vec`, `Crypto.ddt`, `Crypto.ddt_symm`, `Crypto.ddt_eq_ddt_of_inverse`, `Crypto.image_cond`);
  migrated to it on 2026-11-01.

## Statement (verbatim)
> Lemma (DDT of the inverse S-box). Let S be a permutation of F_2^n and S^{-1} its inverse.
> For all a, b ∈ F_2^n:
>   #{x ∈ F_2^n : S(x ⊕ a) ⊕ S(x) = b} = #{y ∈ F_2^n : S^{-1}(y ⊕ b) ⊕ S^{-1}(y) = a}.
> In words: the DDT of S^{-1} is the transpose of the DDT of S.

## Objects, hypotheses, conclusion
| object / hypothesis | in the source | explicit or implicit | Lean |
|---|---|---|---|
| `n`, the block size | `F_2^n` | explicit (no bound on `n`) | a finite index type `ι` (`Fin n` for `n` bits); `n = 0` allowed |
| `F_2^n` with `⊕` | "`F_2^n`", "`⊕`" | explicit | `Crypto.Vec ι` (`ι → ZMod 2`), `+`; words `BitVec n` only in the finite checks, through `toVec` |
| `S` is a permutation of `F_2^n` | "Let S be a permutation" | explicit | `S : Equiv.Perm (Vec ι)` (main); `Function.Bijective S` (`ddt_invFun`) |
| `S^{-1}` is the inverse of `S` | "`S^{-1}` its inverse" | explicit (a definition in the source; two equations `S^{-1} ∘ S = id`, `S ∘ S^{-1} = id` in Lean) | `S.symm`; `Function.invFun S`; or an explicit `T` with `hTS : ∀ x, T (S x) = x`, `hST : ∀ y, S (T y) = y` |
| the two counts | `#{x : …}`, `#{y : …}` | explicit | `Crypto.ddt S a b`, `Crypto.ddt S.symm b a` (natural numbers) |
| `a, b` arbitrary (zero allowed) | "for all a, b" | explicit | `(a b : Vec ι)`, no hypothesis |
| conclusion | the equality of the two counts | explicit | `ddt S a b = ddt S.symm b a` |
| "in words" | the DDT of `S^{-1}` is the transpose of the DDT of `S` | explicit | `ddtMatrix S.symm = (ddtMatrix S).transpose` |

No hypothesis is implicit: the lemma needs nothing beyond "`T` is the inverse of `S`" (and that
hypothesis is needed, see the counterexample). One finding: on the finite set `Vec ι`, the two
equations making up "`T` is the inverse of `S`" are not independent — `T ∘ S = id` alone implies
`S ∘ T = id` (`ddt_eq_ddt_of_leftInverse`).

## Proof plan
The source gives no proof; the standard argument is the change of variable `y = S(x)`.
| step | argument | Lean lemma |
|---|---|---|
| 1 | if `S(x ⊕ a) ⊕ S(x) = b` then `S(x) ⊕ b = S(x ⊕ a)`, so `S^{-1}(S(x) ⊕ b) ⊕ S^{-1}(S(x)) = (x ⊕ a) ⊕ x = a`: the map `x ↦ S(x)` sends the first set into the second (only `S^{-1} ∘ S = id` is used) | `Crypto.image_cond` (library) |
| 2 | step 1 with `(S, a, b)` and `(S^{-1}, b, a)` exchanged sends the second set into the first; the two maps are mutually inverse, so the sets have the same size (`Finset.card_nbij'`) | `Crypto.ddt_eq_ddt_of_inverse` (library) |
| 3 | instantiate with `S^{-1} = S.symm` (`Equiv.Perm`), or `Function.invFun S` (bijective function) | `ddt_symm` (= `Crypto.ddt_symm`, main), `ddt_invFun` |
| 4 | "in words": read entrywise as a matrix transpose | `ddtMatrix_symm` |
| remark | on a finite set one inverse equation suffices (`Finite.injective_iff_surjective`) | `ddt_eq_ddt_of_leftInverse` |

## Finite checks
- Toy instance: `toyS : BitVec 3 → BitVec 3` (a table, `Crypto.Sbox.ofTable`), the 3-cycle
  `5 ↦ 6 ↦ 7 ↦ 5` (identity on `0..4`), with inverse `toyInv` (`5 ↦ 7 ↦ 6 ↦ 5`); `toyInv_toyS`,
  `toyS_toyInv` check they are inverse. The statements are about `Sbox.toFun toyS : Vec (Fin 3) → Vec (Fin 3)`
  and are decided on words through the bridge `Crypto.ddt_toFun`.
  `toy_ddt_transpose`: `ddt (toFun toyS) (toVec a) (toVec b) = ddt (toFun toyInv) (toVec b) (toVec a)`
  for all 64 pairs (`decide`).
  Expected numbers (Python beforehand): `ddt toyS 1 2 = 4`, `ddt toyS 2 1 = 0`, and the inverse has
  them exchanged (`toy_values`).
- Counterexample for the hypothesis "`T` is the inverse of `S`": `T = toyS` itself (not an involution)
  gives `ddt toyS 1 2 = 4 ≠ 0 = ddt toyS 2 1` (`toy_not_symmetric`); `T = id` fails too (`toy_id_fails`).
  There is no counterexample for dropping exactly one of the two inverse equations on `Vec ι`,
  because each implies the other there (`ddt_eq_ddt_of_leftInverse`).

## Status
Check: `check_lean.py Formal/Examples/DdtInverse/Main.lean` → `VERDICT: PASS` on 2026-11-01, before and after the
migration to the library (Lean v4.33.0 + Mathlib v4.33.0); no `sorry`, no `native_decide` /
`bv_decide`, no custom axiom. Every declaration depends at most on `propext, Classical.choice, Quot.sound`.

| source label | Lean declaration | status | axioms | note |
|---|---|---|---|---|
| Lemma (DDT of the inverse S-box) | `DdtInverse.ddt_symm` (= `Crypto.ddt_symm`) | proved | propext, Classical.choice, Quot.sound | `S : Equiv.Perm (Vec ι)`, `S^{-1} = S.symm`; the main theorem |
| same lemma, `S` a bijective function | `DdtInverse.ddt_invFun` | proved | propext, Classical.choice, Quot.sound | `S^{-1} = Function.invFun S` |
| same lemma, explicit inverse `T` (proof engine) | `Crypto.ddt_eq_ddt_of_inverse` (library) | proved | propext, Classical.choice, Quot.sound | hypotheses `T (S x) = x`, `S (T y) = y` |
| remark: one inverse equation suffices on `Vec ι` | `DdtInverse.ddt_eq_ddt_of_leftInverse` | proved | propext, Classical.choice, Quot.sound | only `T (S x) = x` assumed |
| "In words: the DDT of S^{-1} is the transpose of the DDT of S" | `DdtInverse.ddtMatrix_symm` | proved | propext, Classical.choice, Quot.sound | `ddtMatrix S.symm = (ddtMatrix S).transpose` |
| proof step 1 | `Crypto.image_cond` (library) | proved | propext, Classical.choice, Quot.sound | cancellation in characteristic 2 |
| toy instance (3-bit) | `DdtInverse.toy_ddt_transpose`, `toy_values`, `toyInv_toyS`, `toyS_toyInv` | proved by `decide` through `ddt_toFun` | propext, Classical.choice, Quot.sound | expected numbers `4 / 0` confirmed |
| counterexample (`T` not the inverse) | `DdtInverse.toy_not_symmetric`, `toy_id_fails` | proved by `decide` | propext, Classical.choice, Quot.sound | `T = S` and `T = id` both fail at `(a, b) = (1, 2)` |

## Departures from the source
- `F_2^n` is the library carrier `Vec ι` for any finite index type `ι` (more general than `n`-bit
  words; `ι = Fin n` recovers them). `n = 0` is allowed (`Vec (Fin 0)` has one element; the lemma
  holds trivially there). The source presumably has `n ≥ 1` in mind; no hypothesis was added.
- "`S` is a permutation" is encoded as `S : Equiv.Perm (Vec ι)` with `S^{-1} = S.symm`
  (main theorem). Two further spellings of the same lemma are proved so that no reader has to
  convert: a bijective function with Mathlib's `Function.invFun`, and an explicit inverse `T`
  with the two equations `T (S x) = x`, `S (T y) = y` as hypotheses (this last form is the engine).
- `ddt` (the library's `Crypto.ddt`) is defined for every function `S`, not only permutations; the
  count makes sense without bijectivity. Bijectivity enters only through the inverse.
- The finite checks state the facts on `Vec (Fin 3)` and decide them on `BitVec 3` through
  `Crypto.ddt_toFun`; the earlier version defined `ddt` on words directly.
- The `y` of the source's second count is the bound variable `x` of `ddt`; nothing else is renamed.

## Rebuild
```
cd ~/lean-formal && lake build Formal.Examples.DdtInverse.Main && ~/.claude/skills/cipherlean/scripts/check_lean.py Formal/Examples/DdtInverse/Main.lean
```
