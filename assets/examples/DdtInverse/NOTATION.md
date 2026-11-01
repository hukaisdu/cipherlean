# NOTATION — DdtInverse

One row per object. A Lean name denotes exactly one source object; aliases are recorded explicitly.
Source = the user's statement "Lemma (DDT of the inverse S-box)" (2026-11-01), no paper.
Encodings follow the shared library `CipherLean` (`CipherLean/Lib/NOTATION.md`); migrated 2026-11-01.

| source symbol | Lean name | Lean type | meaning | scope / conventions |
|---|---|---|---|---|
| `n` | `ι` with `[Fintype ι] [DecidableEq ι]` | type | the index set of the `n` bits (`Fin n` for words) | `n = Fintype.card ι`; `n = 0` allowed (see README, departures) |
| `F_2^n` | `CipherLean.Vec ι` | `ι → ZMod 2` | the library carrier | `2^n` elements (`CipherLean.card_vec`); words `BitVec n` only in the finite checks |
| `x ⊕ a` | `x + a` | `Vec ι` | xor = addition in characteristic 2 | `CipherLean.add_self`, `CipherLean.add_add_self`; on words `x ^^^ a`, bridged by `CipherLean.toVec_xor` |
| `S` (a permutation of `F_2^n`) | `S : Equiv.Perm (Vec ι)`, used as `⇑S` | `Vec ι ≃ Vec ι` | the S-box, in the main theorem `ddt_symm` | the coercion to a function is inserted automatically in `ddt S a b` |
| `S` (same object, other spelling) | `S : Vec ι → Vec ι` with `hS : Function.Bijective S` | function + hypothesis | the S-box, in `ddt_invFun` | |
| `S` (same object, engine spelling) | `S : Vec ι → Vec ι` together with `T` | function | the S-box, in `CipherLean.ddt_eq_ddt_of_inverse` | no hypothesis on `S` alone; see `T` |
| `S^{-1}` | `S.symm` (main) | `Vec ι ≃ Vec ι` | the inverse permutation | `S.symm_apply_apply : S.symm (S x) = x`, `S.apply_symm_apply : S (S.symm y) = y` |
| `S^{-1}` (same object, other spelling) | `Function.invFun S` | `Vec ι → Vec ι` | Mathlib's noncomputable inverse of a bijection | `Function.leftInverse_invFun hS.1`, `Function.rightInverse_invFun hS.2` |
| `S^{-1}` (same object, engine spelling) | `T` with `hTS : ∀ x, T (S x) = x` and `hST : ∀ y, S (T y) = y` | function + two hypotheses | an explicit two-sided inverse | `hTS` is `Function.LeftInverse T S`, `hST` is `Function.RightInverse T S`; on `Vec ι` each implies the other (`ddt_eq_ddt_of_leftInverse`) |
| `#{x ∈ F_2^n : S(x ⊕ a) ⊕ S(x) = b}` | `CipherLean.ddt S a b` | `ℕ` | DDT entry of `S` at input difference `a`, output difference `b`; `(Finset.univ.filter fun x => S (x + a) + S x = b).card` | unnormalized count, defined for every function `S`; the library's single definition (`CipherLean/Lib/DDT.lean`) |
| `#{y ∈ F_2^n : S^{-1}(y ⊕ b) ⊕ S^{-1}(y) = a}` | `ddt S.symm b a` (resp. `ddt T b a`) | `ℕ` | DDT entry of the inverse at `(b, a)` | the bound variable `y` of the source is the `x` of `ddt` |
| "the DDT of `S`" (as a table) | `ddtMatrix S` | `Matrix (Vec ι) (Vec ι) ℕ` | `ddtMatrix S a b = ddt S a b`; rows = input difference, columns = output difference | `Matrix.of fun a b => ddt S a b`; "transpose" is `Matrix.transpose` |
| toy S-box | `toyS := Sbox.ofTable toyTable`, used as `Sbox.toFun toyS` | `BitVec 3 → BitVec 3`, resp. `Vec (Fin 3) → Vec (Fin 3)` | the 3-cycle `5 ↦ 6 ↦ 7 ↦ 5`, identity on `0..4` | finite checks only; decided on words through `CipherLean.ddt_toFun` |
| toy inverse | `toyInv := Sbox.ofTable toyInvTable` | `BitVec 3 → BitVec 3` | inverse of `toyS` (`5 ↦ 7 ↦ 6 ↦ 5`) | `toyInv_toyS`, `toyS_toyInv` check it |

## Confirmed conventions
- Counts, not probabilities: the statement is about `#{…}`, so `ddt` is a natural number; no division.
- One carrier: statements on `Vec ι`; words appear only in tables and are moved across by `toVec` / `Sbox.toFun`.
- `ddt S a b` puts the input difference first, as in the source's `#{x : S(x ⊕ a) ⊕ S(x) = b}`; "transpose" therefore means `ddtMatrix S.symm a b = ddtMatrix S b a`.
- The source's `x` and `y` are both bound variables of a count; in Lean both are the bound `x` of `ddt`.

## Open questions
- None about the statement. Whether `n ≥ 1` should be required is recorded as a departure (the lemma holds for `n = 0` too).
