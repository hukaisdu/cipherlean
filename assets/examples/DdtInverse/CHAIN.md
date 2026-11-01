# CHAIN — DdtInverse: the proof chain of "Lemma (DDT of the inverse S-box)", for the reader to confirm

Target: `lem:ddt-inverse` (the user's statement of 2026-11-01, no paper; quoted verbatim in README.md).
Read the table from the target down to the definitions. Every row is one thing the proof relies
on; `uses` are the rows it relies on directly. The chain was written before the Lean file and
re-checked against it afterwards (`chain_check.py`).

## Nodes

| id | kind | title | statement | uses | where | implicit | lean | status |
|---|---|---|---|---|---|---|---|---|
| cor:transpose | theorem | DDT of inverse is transpose | "In words: the DDT of S^{-1} is the transpose of the DDT of S", as matrices | lem:ddt-inverse, def:ddtMatrix | source, last sentence | — | DdtInverse.ddtMatrix_symm | proved |
| lem:ddt-inverse | theorem | entrywise identity | For all a, b: #{x : S(x ⊕ a) ⊕ S(x) = b} = #{y : S^{-1}(y ⊕ b) ⊕ S^{-1}(y) = a} | step:bijection, def:ddt, assume:perm | source | none beyond the inverse equations | CipherLean.ddt_symm | proved |
| rem:invFun | lemma | bijective-function spelling | The lemma with S a bijective function and S^{-1} = Function.invFun S | step:bijection, assume:perm | spelling used by Mathlib-style statements | — | DdtInverse.ddt_invFun | proved |
| rem:one-equation | lemma | one inverse equation suffices | On a finite set, T ∘ S = id alone implies S ∘ T = id, so the lemma holds for any left inverse T | step:bijection, assume:perm | finding of the formalization | finiteness of F_2^n | DdtInverse.ddt_eq_ddt_of_leftInverse | proved |
| step:bijection | step | change of variable is a bijection | x ↦ S(x) sends {x : S(x⊕a)⊕S(x)=b} into {y : S^{-1}(y⊕b)⊕S^{-1}(y)=a}, y ↦ S^{-1}(y) sends it back, and the two maps are mutually inverse; hence equal cardinalities | step:image, def:ddt | standard argument (change of variable y = S(x)) | — | CipherLean.ddt_eq_ddt_of_inverse | proved |
| step:image | step | the condition is preserved | If S(x⊕a)⊕S(x) = b then S(x)⊕b = S(x⊕a), hence S^{-1}(S(x)⊕b) ⊕ S^{-1}(S(x)) = (x⊕a)⊕x = a; only S^{-1} ∘ S = id is used | assume:perm | standard argument | about the counted condition only, not the count | CipherLean.image_cond | proved |
| def:ddt | def | DDT entry | #{x ∈ F_2^n : S(x ⊕ a) ⊕ S(x) = b}, an unnormalized count, defined for every function S | — | source | a, b may be zero | CipherLean.ddt | stated |
| def:ddtMatrix | def | DDT as a matrix | the table (a, b) ↦ DDT entry, rows = input difference, columns = output difference | def:ddt | source, "the DDT of S" | — | CipherLean.ddtMatrix | stated |
| assume:perm | assumption | S is a permutation | "Let S be a permutation of F_2^n and S^{-1} its inverse": S bijective, S^{-1} its two-sided inverse | — | source | n = 0 allowed; on F_2^n one of the two inverse equations implies the other | Equiv.Perm | assumed |

`kind`: theorem · lemma · step · def · external · assumption. `uses`: comma-separated ids.
`lean`: the declaration that discharges the row (library lemmas allowed). `status`: pending · stated · proved · cited · assumed.

## External results

None: the source gives no proof and cites nothing; the argument is the standard change of variable.

## Implicit hypotheses found

- None is needed beyond "S^{-1} is the inverse of S"; the counterexamples `toy_not_symmetric` and
  `toy_id_fails` show that hypothesis cannot be dropped.
- On the finite set F_2^n the two inverse equations are not independent (`rem:one-equation`).

## Questions for the reader

- Is n = 0 meant to be excluded? The formal statement allows it (the lemma holds trivially there).

## Dependency graph

`$SKILL/scripts/chain_graph.py CHAIN.md` writes `CHAIN.tex` (TikZ) and compiles `CHAIN.pdf`; the
mermaid version below is kept in sync by the same script.

<!-- chain-graph:begin -->
```mermaid
graph TD
  cortranspose["cor:transpose<br/>DDT of inverse is transpose"]
  lemddtinverse["lem:ddt-inverse<br/>entrywise identity"]
  reminvFun["rem:invFun<br/>bijective-function spelling"]
  remoneequation["rem:one-equation<br/>one inverse equation suffices"]
  stepbijection["step:bijection<br/>change of variable is a bijection"]
  stepimage["step:image<br/>the condition is preserved"]
  defddt["def:ddt<br/>DDT entry"]
  defddtMatrix["def:ddtMatrix<br/>DDT as a matrix"]
  assumeperm["assume:perm<br/>S is a permutation"]
  cortranspose --> lemddtinverse
  cortranspose --> defddtMatrix
  lemddtinverse --> stepbijection
  lemddtinverse --> defddt
  lemddtinverse --> assumeperm
  reminvFun --> stepbijection
  reminvFun --> assumeperm
  remoneequation --> stepbijection
  remoneequation --> assumeperm
  stepbijection --> stepimage
  stepbijection --> defddt
  stepimage --> assumeperm
  defddtMatrix --> defddt
  classDef theorem fill:#dbe6fb,stroke:#1f3a93,stroke-width:3px
  class cortranspose,lemddtinverse theorem
  classDef lemma fill:#eef3fd,stroke:#1f3a93,stroke-width:2px
  class reminvFun,remoneequation lemma
  classDef step fill:#ffffff,stroke:#333,stroke-dasharray:4 3
  class stepbijection,stepimage step
  classDef def fill:#e6e6e6,stroke:#333
  class defddt,defddtMatrix def
  classDef assumption fill:#fdeaea,stroke:#333,stroke-dasharray:1 3
  class assumeperm assumption
```
<!-- chain-graph:end -->
