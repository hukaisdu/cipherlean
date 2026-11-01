/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.DDT
import CipherLean.Lib.Walsh
import Mathlib.Tactic.Ring

/-!
# `CipherLean.Lib.Links` — the DDT and the squared Walsh spectrum are Fourier duals

F. Chabaud and S. Vaudenay, *Links Between Differential and Linear Cryptanalysis*, EUROCRYPT 1994:
for every `F : F_2^ι → F_2^κ` and masks `u`, `v`,

    Σ_{a, b} δ_F(a, b) (-1)^{u·a + v·b} = W_F(u, v)².

Proof as in the paper: expand the square as a double sum over `(x, y)`, substitute `y = x + a`,
and group the inner sum by the output difference `b = F(x + a) + F(x)`.
-/

namespace CipherLean

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Step 1: `W_F(u,v)² = Σ_x Σ_y χ_u(x + y) χ_v(F x + F y)`. -/
theorem walsh_sq_eq_double_sum (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) :
    walsh F u v ^ 2 = ∑ x, ∑ y, chi ℤ u (x + y) * chi ℤ v (F x + F y) := by
  rw [walsh_eq_sum_chi_mul, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [chi_add_right, chi_add_right]; ring

omit [DecidableEq κ] in
/-- Step 2: substitute `y = x + a` in the inner sum. -/
theorem inner_sum_subst (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) (x : Vec ι) :
    ∑ y, chi ℤ u (x + y) * chi ℤ v (F x + F y) =
      ∑ a, chi ℤ u a * chi ℤ v (F (x + a) + F x) := by
  rw [← Equiv.sum_comp (Equiv.addLeft x) (fun y => chi ℤ u (x + y) * chi ℤ v (F x + F y))]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.coe_addLeft]
  rw [← add_assoc, add_self, zero_add, add_comm (F x)]

/-- Step 3: group the sum over inputs by the output difference `b`. -/
theorem sum_chi_diff_eq_sum_ddt (F : Vec ι → Vec κ) (v : Vec κ) (a : Vec ι) :
    ∑ x, chi ℤ v (F (x + a) + F x) = ∑ b, (ddt F a b : ℤ) * chi ℤ v b := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x => F (x + a) + F x)
    (fun x => chi ℤ v (F (x + a) + F x))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hconst : ∀ x ∈ Finset.univ.filter (fun x => F (x + a) + F x = b),
      chi ℤ v (F (x + a) + F x) = chi ℤ v b := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- Chabaud–Vaudenay (EUROCRYPT 1994): `Σ_{a,b} δ_F(a,b) (-1)^{u·a + v·b} = W_F(u,v)²`. -/
theorem sum_ddt_mul_sgn (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) :
    ∑ a, ∑ b, (ddt F a b : ℤ) * sgn ℤ (u ⬝ᵥ a + v ⬝ᵥ b) = walsh F u v ^ 2 := by
  calc ∑ a, ∑ b, (ddt F a b : ℤ) * sgn ℤ (u ⬝ᵥ a + v ⬝ᵥ b)
      = ∑ a, chi ℤ u a * ∑ b, (ddt F a b : ℤ) * chi ℤ v b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold chi; rw [sgn_add]; ring
    _ = ∑ a, chi ℤ u a * ∑ x, chi ℤ v (F (x + a) + F x) := by
        simp only [sum_chi_diff_eq_sum_ddt]
    _ = ∑ a, ∑ x, chi ℤ u a * chi ℤ v (F (x + a) + F x) := by
        simp only [Finset.mul_sum]
    _ = ∑ x, ∑ a, chi ℤ u a * chi ℤ v (F (x + a) + F x) := Finset.sum_comm
    _ = ∑ x, ∑ y, chi ℤ u (x + y) * chi ℤ v (F x + F y) := by
        simp only [inner_sum_subst]
    _ = walsh F u v ^ 2 := (walsh_sq_eq_double_sum F u v).symm

omit [DecidableEq κ] in
/-- Consequence: the DDT determines the squared Walsh spectrum. -/
theorem walsh_sq_eq_of_ddt_eq {F G : Vec ι → Vec κ} (h : ∀ a b, ddt F a b = ddt G a b)
    (u : Vec ι) (v : Vec κ) : walsh F u v ^ 2 = walsh G u v ^ 2 := by
  classical
  rw [← sum_ddt_mul_sgn, ← sum_ddt_mul_sgn]
  simp only [h]

end CipherLean
