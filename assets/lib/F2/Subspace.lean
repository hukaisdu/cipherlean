/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.F2.Vec
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# `CipherLean.Lib.F2.Subspace` — subspaces of `F_2^ι` as finite sets, cosets, annihilators, duality

A subspace is given by its finite set of vectors (`IsSubspace V`: contains `0`, closed under `+`),
so that membership, cosets and annihilators are computable and `decide` can check toy instances.
The duality facts `|V| · |V^⊥| = 2^n` and `V^⊥⊥ = V` come from Mathlib's bilinear-form
orthogonality, through the `ZMod 2`-submodule `toSub hV` with the same underlying set.
The character sum over an annihilator (`sum_chi_ann`) is the lemma behind every coset-average
or fixed-key argument. `natCard_eq_two_pow_finrank` (`#W = 2^{dim W}`) and `exists_le_finrank_eq` (a subspace
of dimension `≥ k` contains one of dimension `k`) are the two dimension facts the ChiChi paper's Theorem 5 needs
(promoted from `WHConj3` on 2026-11-02).
-/

namespace CipherLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `V ≤ F_2^ι` as a finite set: contains `0` and is closed under addition (over `F_2` nothing
more is needed). -/
def IsSubspace (V : Finset (Vec ι)) : Prop :=
  (0 : Vec ι) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a + b ∈ V

instance (V : Finset (Vec ι)) : Decidable (IsSubspace V) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The coset `k + V` (in characteristic 2, `x ∈ k + V ↔ x + k ∈ V`). -/
def coset (V : Finset (Vec ι)) (k : Vec ι) : Finset (Vec ι) :=
  Finset.univ.filter fun x => x + k ∈ V

/-- The annihilator (dual, orthogonal) `V^⊥ = {w : w·v = 0 for all v ∈ V}`. -/
def ann (V : Finset (Vec ι)) : Finset (Vec ι) :=
  Finset.univ.filter fun w => ∀ v ∈ V, w ⬝ᵥ v = 0

theorem mem_coset {V : Finset (Vec ι)} {x k : Vec ι} : x ∈ coset V k ↔ x + k ∈ V := by
  simp [coset]

theorem mem_ann {V : Finset (Vec ι)} {w : Vec ι} : w ∈ ann V ↔ ∀ v ∈ V, w ⬝ᵥ v = 0 := by
  simp [ann]

theorem zero_mem_ann (V : Finset (Vec ι)) : (0 : Vec ι) ∈ ann V := by
  rw [mem_ann]; intro v _; exact zero_dotProduct v

theorem ann_add_mem {V : Finset (Vec ι)} {w₁ w₂ : Vec ι} (h₁ : w₁ ∈ ann V) (h₂ : w₂ ∈ ann V) :
    w₁ + w₂ ∈ ann V := by
  rw [mem_ann] at *
  intro v hv
  rw [add_dotProduct, h₁ v hv, h₂ v hv, add_zero]

/-- The annihilator of any set is a subspace. -/
theorem ann_isSubspace (V : Finset (Vec ι)) : IsSubspace (ann V) :=
  ⟨zero_mem_ann V, fun _ h₁ _ h₂ => ann_add_mem h₁ h₂⟩

omit [Fintype ι] [DecidableEq ι] in
theorem card_pos_of_isSubspace {V : Finset (Vec ι)} (hV : IsSubspace V) : 0 < V.card :=
  Finset.card_pos.mpr ⟨0, hV.1⟩

/-- Every coset has `|V|` elements (translate by `k`). -/
theorem card_coset (V : Finset (Vec ι)) (k : Vec ι) : (coset V k).card = V.card := by
  refine Finset.card_nbij' (· + k) (· + k) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, mem_coset] at hx ⊢
    exact hx
  · intro v hv
    simp only [Finset.mem_coe, mem_coset, add_add_self] at hv ⊢
    exact hv
  · intro x _
    exact add_add_self x k
  · intro v _
    exact add_add_self v k

/-- The number of representatives `k` whose coset contains `x` is `|V|`. -/
theorem card_filter_mem_coset (V : Finset (Vec ι)) (x : Vec ι) :
    (Finset.univ.filter fun k => x + k ∈ V).card = V.card := by
  have : (Finset.univ.filter fun k => x + k ∈ V) = coset V x := by
    ext k; simp [coset, add_comm]
  rw [this, card_coset]

/-- A mask in the annihilator is constant on cosets: `w ∈ V^⊥`, `x ∈ k + V` give `w·x = w·k`. -/
theorem dotProduct_eq_of_mem_ann {V : Finset (Vec ι)} {w x k : Vec ι} (hw : w ∈ ann V)
    (hx : x ∈ coset V k) : w ⬝ᵥ x = w ⬝ᵥ k := by
  have h1 : w ⬝ᵥ (x + k) = 0 := (mem_ann.mp hw) _ (mem_coset.mp hx)
  rw [dotProduct_add] at h1
  exact zmod2_add_eq_zero_iff.mp h1

/-- The character of a mask in `V^⊥` is constant on each coset of `V`. -/
theorem chi_eq_of_mem_ann (K : Type*) [CommRing K] {V : Finset (Vec ι)} {w x k : Vec ι}
    (hw : w ∈ ann V) (hx : x ∈ coset V k) : chi K w x = chi K w k := by
  unfold chi
  rw [dotProduct_eq_of_mem_ann hw hx]

section card
variable {K : Type*} [AddMonoidWithOne K] [CharZero K]

omit [Fintype ι] [DecidableEq ι] in
/-- `|V| ≠ 0` as an element of a characteristic-zero ring (for dividing by `|V|`). -/
theorem card_ne_zero_of_isSubspace {V : Finset (Vec ι)} (hV : IsSubspace V) : (V.card : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (card_pos_of_isSubspace hV).ne'

/-- `|V^⊥| ≠ 0` as an element of a characteristic-zero ring. -/
theorem card_ann_ne_zero (V : Finset (Vec ι)) : ((ann V).card : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨0, zero_mem_ann V⟩).ne'

end card

/-! ## Duality through Mathlib's bilinear forms -/

section duality

/-- The dot product on `F_2^ι` as a bilinear form. -/
def dotForm (ι : Type*) [Fintype ι] : LinearMap.BilinForm (ZMod 2) (Vec ι) :=
  LinearMap.mk₂ (ZMod 2) (fun v w : Vec ι => v ⬝ᵥ w) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

omit [DecidableEq ι] in
@[simp] theorem dotForm_apply (v w : Vec ι) : dotForm ι v w = v ⬝ᵥ w := rfl

omit [DecidableEq ι] in
theorem dotForm_isRefl : (dotForm ι).IsRefl := fun v w h => by
  simpa [dotProduct_comm] using h

omit [DecidableEq ι] in
theorem dotForm_nondegenerate : (dotForm ι).Nondegenerate := by
  classical
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate LinearMap.SeparatingLeft
    LinearMap.SeparatingRight
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · funext i
    have := hm (Pi.single i 1)
    simpa [dotProduct_single] using this
  · funext i
    have := hm (Pi.single i 1)
    simpa [single_dotProduct] using this

/-- The `ZMod 2`-submodule with underlying set `V`. -/
def toSub {V : Finset (Vec ι)} (hV : IsSubspace V) : Submodule (ZMod 2) (Vec ι) :=
  AddSubgroup.toZModSubmodule 2
    { carrier := ↑V
      add_mem' := fun ha hb => hV.2 _ ha _ hb
      zero_mem' := hV.1
      neg_mem' := fun {x} hx => by rw [neg_eq]; exact hx }

omit [Fintype ι] [DecidableEq ι] in
theorem mem_toSub {V : Finset (Vec ι)} (hV : IsSubspace V) {x : Vec ι} :
    x ∈ toSub hV ↔ x ∈ V := Iff.rfl

theorem mem_orthogonal_iff_mem_ann {V : Finset (Vec ι)} (hV : IsSubspace V) {w : Vec ι} :
    w ∈ (dotForm ι).orthogonal (toSub hV) ↔ w ∈ ann V := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_ann]
  constructor
  · intro h v hv
    have := h v ((mem_toSub hV).mpr hv)
    rwa [dotForm_apply, dotProduct_comm] at this
  · intro h v hv
    rw [dotForm_apply, dotProduct_comm]
    exact h v ((mem_toSub hV).mp hv)

omit [Fintype ι] [DecidableEq ι] in
theorem natCard_toSub {V : Finset (Vec ι)} (hV : IsSubspace V) :
    Nat.card (toSub hV) = V.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_toSub hV), Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem natCard_orthogonal {V : Finset (Vec ι)} (hV : IsSubspace V) :
    Nat.card ((dotForm ι).orthogonal (toSub hV)) = (ann V).card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_orthogonal_iff_mem_ann hV),
    Nat.card_eq_fintype_card, Fintype.card_coe]

/-- `|V| · |V^⊥| = 2^n`. -/
theorem card_mul_card_ann {V : Finset (Vec ι)} (hV : IsSubspace V) :
    V.card * (ann V).card = 2 ^ Fintype.card ι := by
  have hK : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have h1 : V.card = 2 ^ Module.finrank (ZMod 2) (toSub hV) := by
    have : Module.Finite (ZMod 2) (toSub hV) := Module.Finite.of_finite
    rw [← natCard_toSub hV, Module.natCard_eq_pow_finrank (K := ZMod 2), hK]
  have h2 : (ann V).card = 2 ^ Module.finrank (ZMod 2) ((dotForm ι).orthogonal (toSub hV)) := by
    have : Module.Finite (ZMod 2) ((dotForm ι).orthogonal (toSub hV)) := Module.Finite.of_finite
    rw [← natCard_orthogonal hV, Module.natCard_eq_pow_finrank (K := ZMod 2), hK]
  have h3 := LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate (toSub hV)
  have h4 : Module.finrank (ZMod 2) (toSub hV) ≤ Module.finrank (ZMod 2) (Vec ι) :=
    Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card] at h3 h4
  rw [h1, h2, h3, ← pow_add, Nat.add_sub_cancel' h4]

/-- A vector outside `V` is detected by a mask in `V^⊥` (this is `V^⊥⊥ ⊆ V`). -/
theorem exists_ann_dot_ne {V : Finset (Vec ι)} (hV : IsSubspace V) {y : Vec ι} (hy : y ∉ V) :
    ∃ w ∈ ann V, w ⬝ᵥ y ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  apply hy
  rw [← mem_toSub hV,
    ← LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl (toSub hV),
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [dotForm_apply]
  exact hcon n ((mem_orthogonal_iff_mem_ann hV).mp hn)

/-- `V^⊥⊥ = V` for a subspace `V`. -/
theorem ann_ann {V : Finset (Vec ι)} (hV : IsSubspace V) : ann (ann V) = V := by
  ext y
  rw [mem_ann]
  constructor
  · intro h
    by_contra hy
    obtain ⟨w, hw, hne⟩ := exists_ann_dot_ne hV hy
    exact hne (by rw [dotProduct_comm]; exact h w hw)
  · intro hy w hw
    rw [dotProduct_comm]
    exact (mem_ann.mp hw) y hy

theorem card_ann_mul_card {V : Finset (Vec ι)} (hV : IsSubspace V) :
    (ann V).card * V.card = 2 ^ Fintype.card ι := by
  rw [mul_comm]; exact card_mul_card_ann hV

end duality

/-! ## The character sum over an annihilator -/

section chi
variable (K : Type*) [CommRing K]

/-- `Σ_{w ∈ V^⊥} (-1)^{w·y}` is `|V^⊥|` for `y ∈ V` and `0` otherwise (pair `w` with `w + w₀`
where `w₀·y = 1`). -/
theorem sum_chi_ann {V : Finset (Vec ι)} (hV : IsSubspace V) (y : Vec ι) :
    ∑ w ∈ ann V, chi K w y = if y ∈ V then ((ann V).card : K) else 0 := by
  split_ifs with hy
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_congr rfl fun w hw => chi_eq_one K ((mem_ann.mp hw) y hy)
  · obtain ⟨w₀, hw₀, hne⟩ := exists_ann_dot_ne hV hy
    refine Finset.sum_involution (fun w _ => w + w₀) ?_ ?_ ?_ ?_
    · intro w _
      rw [chi_add_left, chi_eq_neg_one K hne]
      ring
    · intro w _ _ h
      have h0 : w₀ = 0 := add_eq_left.mp h
      exact hne (by rw [h0]; exact zero_dotProduct y)
    · intro w hw
      exact ann_add_mem hw hw₀
    · intro w _
      exact add_add_self w w₀

/-- The same sum over a subspace `V` itself, by duality: `|V|` for `y ∈ V^⊥` and `0` otherwise. -/
theorem sum_chi_subspace {V : Finset (Vec ι)} (hV : IsSubspace V) (y : Vec ι) :
    ∑ w ∈ V, chi K w y = if y ∈ ann V then (V.card : K) else 0 := by
  have h := sum_chi_ann K (ann_isSubspace V) y
  rw [ann_ann hV] at h
  exact h

end chi

/-! ## Dimension and size of a subspace -/

section finrank

omit [Fintype ι] [DecidableEq ι] in
/-- A binary vector space of dimension `k` has `2^k` elements: the bridge from a count to a
dimension. -/
theorem natCard_eq_two_pow_finrank [Finite ι] (W : Submodule (ZMod 2) (Vec ι)) :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- A subspace of dimension at least `k` contains a subspace of dimension exactly `k`: the span of
the first `k` vectors of a basis (any field; no Mathlib lemma states it). -/
theorem exists_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) {k : ℕ} (hk : k ≤ Module.finrank K W) :
    ∃ A : Submodule K V, A ≤ W ∧ Module.finrank K A = k := by
  classical
  let bW := Module.finBasis K W
  let g : Fin k → W := fun i => bW (Fin.castLE hk i)
  let f : Fin k → V := fun i => (g i : V)
  refine ⟨Submodule.span K (Set.range f), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (g i).2
  · have hg : LinearIndependent K g :=
      bW.linearIndependent.comp (Fin.castLE hk) (Fin.castLE_injective hk)
    have hf : LinearIndependent K f := by
      have := hg.map (f := W.subtype) (by rw [Submodule.ker_subtype]; exact disjoint_bot_right)
      simpa [f, g, Function.comp_def] using this
    rw [finrank_span_eq_card hf, Fintype.card_fin]

end finrank

end CipherLean
