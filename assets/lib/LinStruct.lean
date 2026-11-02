/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.DDT

/-!
# `CipherLean.Lib.LinStruct` — linear structures of a Boolean function; the space `E_λ` of a map

`IsLinStruct f a` says that the derivative `Δ_a f(x) = f(x + a) + f(x)` of the Boolean function
`f : F_2^ι → F_2` is constant (Lai 1994; Carlet 2021 §2.3): the linear structures of `f`. They are
closed under addition (`isLinStruct_add`, from `Δ_{a+a′} f(x) = Δ_a f(x + a′) + Δ_{a′} f(x)`), and the
constant is `f(a) + f(0)` (`isLinStruct_iff`).

For a vectorial map `H : F_2^ι → F_2^ι` and a mask `λ`, `Elam H lam` is the ChiChi paper's
`E_λ = {α : λ ∈ K_H(α)}` (§7.1): the directions `α` such that `⟨λ, d⟩` is constant on the output
differences `S_α = outputDiffs H α` — equivalently (`mem_Elam_iff_isLinStruct`) the linear structures of
the component `⟨λ, H⟩`, which makes it a `ZMod 2`-submodule (the paper's Lemma 22). It is the dual
of `KH`: `KH F α` fixes the difference and varies the mask, `Elam H lam` fixes the mask and varies
the difference; for `H = F⁻¹` the two are related by `mem_Elam_iff_mem_KH`. The §2.1 spelling through
the differential–linear bias, `E_λ = {α : Bias(α, λ) = ±1}`, is `mem_Elam_iff_bias` (unnormalized: the sign
sum is `±2^N`). Membership is decidable, for finite checks.

Promoted from `WHConj3` (Theorem 5, piece C) on 2026-11-02.
-/

namespace CipherLean

variable {ι : Type*}

/-- `a` is a linear structure of `f : F_2^ι → F_2` when `Δ_a f` is constant (Carlet 2021 §2.3). -/
def IsLinStruct (f : Vec ι → ZMod 2) (a : Vec ι) : Prop := ∃ c, ∀ x, f (x + a) + f x = c

theorem isLinStruct_zero (f : Vec ι → ZMod 2) : IsLinStruct f 0 :=
  ⟨0, fun x => by rw [add_zero, CharTwo.add_self_eq_zero]⟩

/-- The linear structures are closed under addition:
`Δ_{a+a′} f(x) = Δ_a f(x + a′) + Δ_{a′} f(x)` (the classical "LS(f) is a subspace", Lai 1994). -/
theorem isLinStruct_add {f : Vec ι → ZMod 2} {a a' : Vec ι} (ha : IsLinStruct f a)
    (ha' : IsLinStruct f a') : IsLinStruct f (a + a') := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨c', hc'⟩ := ha'
  refine ⟨c + c', fun x => ?_⟩
  have h1 := hc (x + a')
  have h2 := hc' x
  calc f (x + (a + a')) + f x
      = (f (x + a' + a) + f (x + a')) + (f (x + a') + f x) := by
        rw [zmod2_add_add_add, add_comm a a', ← add_assoc]
    _ = c + c' := by rw [h1, h2]

/-- The constant of a linear structure is `Δ_a f(0) = f(a) + f(0)`. -/
theorem isLinStruct_iff (f : Vec ι → ZMod 2) (a : Vec ι) :
    IsLinStruct f a ↔ ∀ x, f (x + a) + f x = f a + f 0 := by
  constructor
  · rintro ⟨c, hc⟩ x
    have h0 := hc 0
    rw [zero_add] at h0
    rw [hc x, h0]
  · intro h
    exact ⟨f a + f 0, h⟩

/-! ## `E_λ`: the directions on which the component `⟨λ, H⟩` has a constant derivative -/

variable [Fintype ι] [DecidableEq ι]

/-- Being a linear structure is decidable on a finite domain (through the constant `f(a) + f(0)`). -/
instance (f : Vec ι → ZMod 2) (a : Vec ι) : Decidable (IsLinStruct f a) :=
  decidable_of_iff (∀ x, f (x + a) + f x = f a + f 0) (isLinStruct_iff f a).symm

/-- `λ` is constant on the output differences of `H` at `α` iff `α` is a linear structure of the
component `⟨λ, H⟩`. -/
theorem constMasks_outputDiffs_iff_isLinStruct (H : Vec ι → Vec ι) (α lam : Vec ι) :
    lam ∈ constMasks (outputDiffs H α) ↔ IsLinStruct (fun y => lam ⬝ᵥ H y) α := by
  rw [mem_constMasks]
  constructor
  · intro h
    refine ⟨lam ⬝ᵥ H (0 + α) + lam ⬝ᵥ H 0, fun x => ?_⟩
    have := h _ (mem_outputDiffs.mpr ⟨x, rfl⟩) _ (mem_outputDiffs.mpr ⟨0, rfl⟩)
    simpa [deriv, dotProduct_add] using this
  · rintro ⟨c, hc⟩ d hd d' hd'
    obtain ⟨y, rfl⟩ := mem_outputDiffs.mp hd
    obtain ⟨y', rfl⟩ := mem_outputDiffs.mp hd'
    simp only [deriv, dotProduct_add]
    exact (hc y).trans (hc y').symm

/-- The ChiChi paper's `E_λ = {α ∈ F^N : λ ∈ K_H(α)}` (§7.1), with `K_H(α)` the masks constant on
`S_α = outputDiffs H α`, for any map `H`; a subspace because the linear structures of `⟨λ, H⟩` are
closed under addition (the paper's Lemma 22). -/
def Elam (H : Vec ι → Vec ι) (lam : Vec ι) : Submodule (ZMod 2) (Vec ι) where
  carrier := {α | lam ∈ constMasks (outputDiffs H α)}
  zero_mem' := (constMasks_outputDiffs_iff_isLinStruct H 0 lam).mpr (isLinStruct_zero _)
  add_mem' := fun {a c} (ha : lam ∈ constMasks (outputDiffs H a))
      (hc : lam ∈ constMasks (outputDiffs H c)) =>
    (constMasks_outputDiffs_iff_isLinStruct H (a + c) lam).mpr
      (isLinStruct_add ((constMasks_outputDiffs_iff_isLinStruct H a lam).mp ha)
        ((constMasks_outputDiffs_iff_isLinStruct H c lam).mp hc))
  smul_mem' := fun r {a} (ha : lam ∈ constMasks (outputDiffs H a)) => by
    rcases zmod2_cases r with rfl | rfl
    · rw [zero_smul]
      exact (constMasks_outputDiffs_iff_isLinStruct H 0 lam).mpr (isLinStruct_zero _)
    · rw [one_smul]
      exact ha

theorem mem_Elam {H : Vec ι → Vec ι} {lam α : Vec ι} :
    α ∈ Elam H lam ↔ lam ∈ constMasks (outputDiffs H α) := Iff.rfl

/-- `E_λ` is the set of linear structures of the component `H_λ = ⟨λ, H⟩` (§2.3 of the paper). -/
theorem mem_Elam_iff_isLinStruct {H : Vec ι → Vec ι} {lam α : Vec ι} :
    α ∈ Elam H lam ↔ IsLinStruct (fun y => lam ⬝ᵥ H y) α :=
  constMasks_outputDiffs_iff_isLinStruct H α lam

/-- Membership is decidable through the constant `Δ_α H_λ(0)` (one pass over the inputs), for
finite checks. -/
instance (H : Vec ι → Vec ι) (lam α : Vec ι) : Decidable (α ∈ Elam H lam) :=
  decidable_of_iff (∀ x, lam ⬝ᵥ H (x + α) + lam ⬝ᵥ H x = lam ⬝ᵥ H α + lam ⬝ᵥ H 0)
    (mem_Elam_iff_isLinStruct.trans (isLinStruct_iff _ _)).symm

/-- For `H = F⁻¹`, `α ∈ E_λ` iff `λ ∈ KH F α`: the two spaces are dual readings of one condition. -/
theorem mem_Elam_iff_mem_KH {F : Vec ι → Vec ι} (hbij : Function.Bijective F) {lam α : Vec ι} :
    α ∈ Elam (Equiv.ofBijective F hbij).symm lam ↔ lam ∈ KH F α := by
  rw [mem_Elam, KH_eq_constMasks_outputDiffs hbij]

/-- `λ = 0` lies in every `K_H(α)`: `E_0 = F^N` for every map. -/
theorem Elam_zero (H : Vec ι → Vec ι) : Elam H 0 = ⊤ := by
  rw [eq_top_iff]
  intro α _
  rw [mem_Elam]
  exact Submodule.zero_mem _

/-- A linear `H` (the identity) has `E_λ = F^N` for every `λ`. -/
theorem Elam_id (lam : Vec ι) : Elam (id : Vec ι → Vec ι) lam = ⊤ := by
  rw [eq_top_iff]
  intro α _
  rw [mem_Elam_iff_isLinStruct]
  refine ⟨lam ⬝ᵥ α, fun x => ?_⟩
  simp only [id, dotProduct_add]
  rw [add_comm (lam ⬝ᵥ x), add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The §2.1 spelling of the ChiChi paper: `E_λ = {α : Bias(α, λ) = ±1}`, with the bias unnormalized
(`∑ y, (−1)^{⟨λ, H(y+α)+H(y)⟩} = ±2^N`). -/
theorem mem_Elam_iff_bias {H : Vec ι → Vec ι} {lam α : Vec ι} :
    α ∈ Elam H lam ↔
      ((∑ y, chi ℤ lam (deriv H α y)) = 2 ^ Fintype.card ι ∨
        (∑ y, chi ℤ lam (deriv H α y)) = -(2 ^ Fintype.card ι)) := by
  rw [mem_Elam, sum_chi_deriv_eq_iff_mem_constMasks]

/-! ## Finite checks on `F_2^2` -/

/-- For `H(x) = (x_0 x_1, 0)` on `F_2^2`: the component `⟨(1,0), H⟩ = x_0 x_1` has no nonzero linear
structure (`E_{(1,0)} = {0}`), while `⟨(0,1), H⟩ = 0` has all four (`E_{(0,1)} = ⊤`). -/
theorem Elam_quadratic_example :
    (∀ α : Vec (Fin 2), α ∈ Elam (fun x : Vec (Fin 2) => ![x 0 * x 1, 0]) ![1, 0] → α = 0) ∧
      (![1, 0] : Vec (Fin 2)) ∈ Elam (fun x : Vec (Fin 2) => ![x 0 * x 1, 0]) ![0, 1] := by
  decide +kernel

/-- `(0,1)` is a linear structure of `x_0` and `(1,1)` is not one of `x_0 x_1`. -/
theorem isLinStruct_example :
    IsLinStruct (fun x : Vec (Fin 2) => x 0) ![0, 1] ∧
      ¬ IsLinStruct (fun x : Vec (Fin 2) => x 0 * x 1) ![1, 1] := by
  decide +kernel

end CipherLean
