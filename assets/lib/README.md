# `CipherLean` — shared Lean 4 library for cryptanalysis statements

Reusable definitions and lemmas that every paper formalization in this workspace imports instead
of re-defining: the carrier `F_2^ι`, characters, subspaces with duality, Walsh coefficients,
the DDT, table S-boxes. Carrier decision and symbol table: `NOTATION.md` (this directory).
Created 2026-11-01 by harvesting `CosetSpectrum`, `Examples/*` and `DdtInverse` (which had used
three different encodings of `F_2^n`); extended the same day with the second harvest found by
`scripts/promote_candidates.py` (halfspace identity, DDT matrix form and inverse spellings, masks
constant on cosets, cardinality casts), and on 2026-11-02 with the third harvest from `WHConj3`
(derivative and difference sets of a map, the χ map, two gluing lemmas).

## Modules

| module | contents | status |
|---|---|---|
| `CipherLean.Lib.F2.Vec` | `Vec ι`, `F_2` facts (`add_self`, `add_add_self`, `add_eq_iff_eq_add`), `sum_elim_eq_iff` (two words), `card_vec`, `sgn`, `chi`, `sum_chi` (orthogonality), bridge `toVec`/`ofVec`/`bvEquiv`, `toVec_xor`, `card_bitVec`, `single_dot`, `filter_ne_zero_eq` | PASS |
| `CipherLean.Lib.F2.Subspace` | `IsSubspace` (decidable), `coset`, `ann`, `card_coset`, `dotForm` (nondegenerate, reflexive), `toSub`, `card_mul_card_ann`, `exists_ann_dot_ne`, `ann_ann`, `sum_chi_ann`, `sum_chi_subspace`, `dotProduct_eq_of_mem_ann`, `chi_eq_of_mem_ann`, `card_ne_zero_of_isSubspace`, `card_ann_ne_zero` | PASS |
| `CipherLean.Lib.Sbox` | `ofTable`, `toFun`, `toFun_bijective`, `toPerm`, `bijective_of_injective`, PRESENT (`present`, `presentVec`, bijective by `decide`) | PASS |
| `CipherLean.Lib.Walsh` | `walsh`, `linCount`, `correlation`, `walsh_eq_two_mul_linCount_sub`, `walsh_zero_zero`, `walsh_zero_right`, `walsh_zero_left_of_bijective`, `sum_walsh_sq` (Parseval), the halfspace identity `halfSum`, `walsh_single_eq_sub`, `halfSum_add_halfSum`, `walsh_single_eq_two_mul_halfSum`, `pow_dvd_halfSum`, PRESENT values | PASS |
| `CipherLean.Lib.DDT` | `ddt`, `deriv`, `inputDiffs`, `outputDiffs`, `mem_inputDiffs_iff_ddt_ne_zero`, `outputDiffs_inv_eq_inputDiffs` (the viewpoint table), `ddt_row_sum`, `ddt_zero_left`, `even_ddt`, `ddt_eq_ddt_of_inverse`, `ddt_symm`, `diffUniformity`, `ddt_le_diffUniformity`, `diffUniformity_le_iff`, `IsAPN`, `ddt_invFun`, `ddt_eq_ddt_of_leftInverse`, `ddtMatrix`, `ddtMatrix_symm`, bridge `ddt_toFun`, `ddt_toFun_row_sum`, `diffUniformity_toFun_le_iff`, PRESENT `δ = 4` | PASS |
| `CipherLean.Lib.Links` | Chabaud–Vaudenay: `sum_ddt_mul_sgn` (`Σ_{a,b} δ_F(a,b)(-1)^{u·a+v·b} = W_F(u,v)²`), `walsh_sq_eq_of_ddt_eq` | PASS |
| `CipherLean.Lib.Chi` | `chiMap` (Keccak χ on a cycle of length `r`), `deriv_chiMap_apply`, `chiMap_three_bijective`, `chiMap_four_not_bijective` | PASS |
| `CipherLean` | umbrella import | — |

Status is the verdict of `check_lean.py` (no `sorry`, standard axioms only; the finite checks on
PRESENT use `decide +kernel`, which adds no axiom).

## Use

```lean
import CipherLean
open CipherLean
-- F : Vec ι → Vec κ, masks u v, differences a b; `walsh F u v`, `ddt F a b`, `ann V`, ...
```

Toy instances: define the S-box on words (`Sbox.ofTable`), move it to `F_2^n` with `Sbox.toFun`,
and decide DDT facts through `ddt_toFun` / `diffUniformity_toFun_le_iff` (kernel evaluation on
`BitVec` is fast; on `Vec (Fin 4)` one DDT row costs about a minute).

## Extend (the promotion rule)

A lemma proved for a paper that is general in the index type and speaks about a library object
(Walsh coefficient, DDT, subspace, S-box) moves here before the paper directory is closed: add it
with a docstring naming the source, add a finite check if it is a definition, rebuild with
`$SKILL/scripts/lake_build.sh CipherLean`, run `check_lean.py` on the module, and add the row to
`NOTATION.md`. Do not add paper-specific objects (a particular cipher's state, a specific theorem's
auxiliary function); those stay in `CipherLean/<Slug>/`.

## Conventions

- Statistics are integers or counts; normalized quantities (`correlation`) are corollary definitions.
- `K` in `sgn K` / `chi K` is any commutative ring; use `ℤ` unless a division is needed.
- `toVec x i` is bit `i` of `x`, least significant bit first; a mask written as a word `u : BitVec n`
  becomes `toVec u`.
- Sources: C. Carlet, *Boolean Functions for Cryptography and Coding Theory*, CUP 2021 (definitions);
  K. Nyberg, EUROCRYPT 1993 (differential uniformity); F. Chabaud, S. Vaudenay, EUROCRYPT 1994
  (DDT ↔ Walsh link); A. Bogdanov et al., CHES 2007 (PRESENT).

## Rebuild and check

```
cd ~/cipherlean
~/.claude/skills/cipherlean/scripts/lake_build.sh CipherLean
for m in F2/Vec F2/Subspace Sbox Walsh DDT Links; do
  ~/.claude/skills/cipherlean/scripts/check_lean.py CipherLean/Lib/$m.lean --no-build
done
```
