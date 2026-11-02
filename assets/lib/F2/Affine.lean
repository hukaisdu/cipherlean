/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.F2.Vec
import CipherLean.Lib.F2.Subspace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# `CipherLean.Lib.F2.Affine` — masks constant on a set, the hyperplane `λ^⊥`, direction spaces

Three `ZMod 2`-submodules of `Vec ι` behind every "a mask is constant on a set of differences"
argument. `constMasks S` is the set of masks `λ` with `⟨λ, d⟩ = ⟨λ, d′⟩` for all `d, d′ ∈ S` (the
pairwise reading of "constant"; a subspace, `⊤` when `S` has at most one element).
`perp λ = {w : ⟨λ, w⟩ = 0}` is the hyperplane annihilated by one mask (the `Finset` annihilator of
a set of vectors is `ann V` in `F2/Subspace.lean`). `dirAff T = span{t + t′ : t, t′ ∈ T}` is the
direction space of the affine hull of `T`: the span of `{t + t⁰ : t ∈ T}` for any anchor `t⁰ ∈ T`,
written without choosing the anchor, and `⊥` for `T = ∅`. `dirAff_le_perp_iff` is the link: `λ`
annihilates `dir Aff T` iff `⟨λ, t + t′⟩ = 0` for all `t, t′ ∈ T`, i.e. iff `λ ∈ constMasks T`; so
`constMasks S = (dotForm ι).orthogonal (dirAff S)` (`constMasks_eq_orthogonal_dirAff`), with the dimension and
cardinality sentences `finrank_constMasks_add_finrank_dirAff`, `natCard_constMasks` — the ChiChi paper's Lemma 1
(promoted from `WHConj3`, piece C, 2026-11-02).

Source: the ChiChi paper, §2.1 "The four spaces" (`K_H(α)`, `dir`) and App. C.1 (the empty-set
convention); promoted from `WHConj3` (Lemma 24, piece B) on 2026-11-02. `K_H(α)` itself, the masks
constant on the attainable differences of a map, is `KH` in `Lib/DDT.lean`.
-/

namespace CipherLean

variable {ι : Type*} [Fintype ι]

/-- The masks `λ` for which `⟨λ, d⟩` is constant on the finite set `S`, read pairwise
(`⟨λ, d⟩ = ⟨λ, d′⟩` for all `d, d′ ∈ S`); a subspace of `F_2^ι`. -/
def constMasks (S : Finset (Vec ι)) : Submodule (ZMod 2) (Vec ι) where
  carrier := {lam | ∀ d ∈ S, ∀ d' ∈ S, lam ⬝ᵥ d = lam ⬝ᵥ d'}
  zero_mem' := fun _ _ _ _ => by simp
  add_mem' := fun {a c} (ha : ∀ d ∈ S, ∀ d' ∈ S, a ⬝ᵥ d = a ⬝ᵥ d')
      (hc : ∀ d ∈ S, ∀ d' ∈ S, c ⬝ᵥ d = c ⬝ᵥ d') d hd d' hd' => by
    rw [add_dotProduct, add_dotProduct, ha d hd d' hd', hc d hd d' hd']
  smul_mem' := fun r {a} (ha : ∀ d ∈ S, ∀ d' ∈ S, a ⬝ᵥ d = a ⬝ᵥ d') d hd d' hd' => by
    rw [smul_dotProduct, smul_dotProduct, ha d hd d' hd']

theorem mem_constMasks {S : Finset (Vec ι)} {lam : Vec ι} :
    lam ∈ constMasks S ↔ ∀ d ∈ S, ∀ d' ∈ S, lam ⬝ᵥ d = lam ⬝ᵥ d' := Iff.rfl

instance (S : Finset (Vec ι)) (lam : Vec ι) : Decidable (lam ∈ constMasks S) :=
  decidable_of_iff _ mem_constMasks.symm

/-- The hyperplane `λ^⊥ = {w : ⟨λ, w⟩ = 0}` annihilated by one mask. -/
def perp (lam : Vec ι) : Submodule (ZMod 2) (Vec ι) where
  carrier := {w | lam ⬝ᵥ w = 0}
  zero_mem' := dotProduct_zero lam
  add_mem' := fun {a c} (ha : lam ⬝ᵥ a = 0) (hc : lam ⬝ᵥ c = 0) => by
    change lam ⬝ᵥ (a + c) = 0
    rw [dotProduct_add, ha, hc, add_zero]
  smul_mem' := fun r {w} (hw : lam ⬝ᵥ w = 0) => by
    change lam ⬝ᵥ (r • w) = 0
    rw [dotProduct_smul, hw, smul_zero]

theorem mem_perp {lam w : Vec ι} : w ∈ perp lam ↔ lam ⬝ᵥ w = 0 := Iff.rfl

instance (lam w : Vec ι) : Decidable (w ∈ perp lam) := decidable_of_iff _ mem_perp.symm

/-- `dir(Aff T) = span{t + t⁰ : t ∈ T}` for any `t⁰ ∈ T`, written without choosing the anchor as
the span of all pairwise sums; `⊥` for `T = ∅`. -/
def dirAff (T : Finset (Vec ι)) : Submodule (ZMod 2) (Vec ι) :=
  Submodule.span (ZMod 2) {v | ∃ t ∈ T, ∃ t' ∈ T, v = t + t'}

/-- `λ` annihilates `dir Aff T` iff `⟨λ, t + t′⟩ = 0` for all `t, t′ ∈ T`. -/
theorem dirAff_le_perp_iff {T : Finset (Vec ι)} {lam : Vec ι} :
    dirAff T ≤ perp lam ↔ ∀ t ∈ T, ∀ t' ∈ T, lam ⬝ᵥ (t + t') = 0 := by
  rw [dirAff, Submodule.span_le]
  constructor
  · intro h t ht t' ht'
    exact h ⟨t, ht, t', ht', rfl⟩
  · rintro h v ⟨t, ht, t', ht', rfl⟩
    exact h t ht t' ht'

/-! ## The masks constant on a set are the orthogonal complement of its direction space

The ChiChi paper's Lemma 1 (§3.1, `K_H(α) = dir(D_α)^⊥`, `dim K_H(α) = N − dim D_α`,
`#K_H(α) = 2^{N − dim D_α}`), for any finite set `S` of differences and without choosing an anchor
`d^(0) ∈ S`: pairwise constancy is annihilating all pairwise sums (`dirAff_le_perp_iff`). -/

/-- `constMasks S` is the orthogonal complement of `dir Aff S` for the dot product. -/
theorem constMasks_eq_orthogonal_dirAff (S : Finset (Vec ι)) :
    constMasks S = (dotForm ι).orthogonal (dirAff S) := by
  ext lam
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_constMasks]
  constructor
  · intro h n hn
    have hle : dirAff S ≤ perp lam := dirAff_le_perp_iff.mpr fun t ht t' ht' => by
      rw [dotProduct_add, zmod2_add_eq_zero_iff]
      exact h t ht t' ht'
    have := hle hn
    rw [mem_perp] at this
    rw [dotForm_apply, dotProduct_comm]
    exact this
  · intro h d hd d' hd'
    have hle : dirAff S ≤ perp lam := fun n hn => by
      rw [mem_perp, dotProduct_comm]
      simpa using h n hn
    have := dirAff_le_perp_iff.mp hle d hd d' hd'
    rwa [dotProduct_add, zmod2_add_eq_zero_iff] at this

/-- `dim constMasks S + dim dir Aff S = n` (orthogonal-complement dimension for the nondegenerate
dot product). -/
theorem finrank_constMasks_add_finrank_dirAff (S : Finset (Vec ι)) :
    Module.finrank (ZMod 2) (constMasks S) + Module.finrank (ZMod 2) (dirAff S) =
      Fintype.card ι := by
  rw [constMasks_eq_orthogonal_dirAff,
    LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate,
    Module.finrank_fintype_fun_eq_card]
  have := Submodule.finrank_le (dirAff S)
  rw [Module.finrank_fintype_fun_eq_card] at this
  omega

/-- `#constMasks S = 2^{n − dim dir Aff S}`. -/
theorem natCard_constMasks (S : Finset (Vec ι)) :
    Nat.card (constMasks S) = 2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (dirAff S)) := by
  rw [natCard_eq_two_pow_finrank]
  congr 1
  have := finrank_constMasks_add_finrank_dirAff S
  omega

/-! ## Finite checks on `F_2^2` -/

/-- The masks constant on `{(1,0), (1,1)}` are those with `λ_1 = 0`. -/
theorem constMasks_example :
    (![1, 0] : Vec (Fin 2)) ∈ constMasks ({![1, 0], ![1, 1]} : Finset (Vec (Fin 2))) ∧
      (![0, 1] : Vec (Fin 2)) ∉ constMasks ({![1, 0], ![1, 1]} : Finset (Vec (Fin 2))) := by
  decide

/-- `(0,1) ∈ (1,0)^⊥` and `(1,1) ∉ (1,0)^⊥`. -/
theorem perp_example :
    (![0, 1] : Vec (Fin 2)) ∈ perp ![1, 0] ∧ (![1, 1] : Vec (Fin 2)) ∉ perp ![1, 0] := by
  decide

/-- `dir Aff {(1,0), (1,1)} = span{(0,1)}`: annihilated by `(1,0)`, not by `(0,1)`. -/
theorem dirAff_example :
    dirAff ({![1, 0], ![1, 1]} : Finset (Vec (Fin 2))) ≤ perp ![1, 0] ∧
      ¬ dirAff ({![1, 0], ![1, 1]} : Finset (Vec (Fin 2))) ≤ perp ![0, 1] := by
  constructor
  · rw [dirAff_le_perp_iff]; decide
  · rw [dirAff_le_perp_iff]; decide

end CipherLean
