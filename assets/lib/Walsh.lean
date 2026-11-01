/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.Sbox
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# `CipherLean.Lib.Walsh` — Walsh coefficients, linear-approximation counts, Parseval

For a vectorial function `F : F_2^ι → F_2^κ` and masks `u`, `v`, the Walsh coefficient is
`W_F(u, v) = Σ_x (-1)^{u·x + v·F(x)}` (Carlet 2021, §2.2.1, written there as
`W_F(u, v) = Σ_x (-1)^{v·F(x) + u·x}`). It is kept as an integer; the correlation `W/2^n` and the
LAT entry `W/2` are corollary definitions, because division is total in Lean and a theorem about
them can hold for the wrong reason. `linCount F u v = #{x : u·x = v·F(x)}` is the count that
linear cryptanalysis estimates, and `walsh_eq_two_mul_linCount_sub` is the conversion.
-/

namespace CipherLean

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Walsh coefficient `W_F(u, v) = Σ_x (-1)^{u·x + v·F(x)}`, an unnormalized integer. -/
def walsh (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) : ℤ :=
  ∑ x, sgn ℤ (u ⬝ᵥ x + v ⬝ᵥ F x)

/-- The number of inputs where the linear approximation `u·x = v·F(x)` holds. -/
def linCount (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) : ℕ :=
  (Finset.univ.filter fun x => u ⬝ᵥ x = v ⬝ᵥ F x).card

/-- The correlation `c_F(u, v) = W_F(u, v) / 2^n` (a corollary form; state theorems on `walsh`). -/
def correlation (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) : ℚ :=
  walsh F u v / 2 ^ Fintype.card ι

theorem walsh_eq_sum_chi_mul (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) :
    walsh F u v = ∑ x, chi ℤ u x * chi ℤ v (F x) := by
  unfold walsh chi
  simp only [sgn_add]

/-- Conversion between the Walsh coefficient and the count:
`W_F(u,v) = 2·#{x : u·x = v·F(x)} − 2^n`. -/
theorem walsh_eq_two_mul_linCount_sub (F : Vec ι → Vec κ) (u : Vec ι) (v : Vec κ) :
    walsh F u v = 2 * (linCount F u v : ℤ) - 2 ^ Fintype.card ι := by
  unfold walsh linCount sgn
  have h : ∀ x : Vec ι, (if u ⬝ᵥ x + v ⬝ᵥ F x = 0 then (1 : ℤ) else -1) =
      2 * (if u ⬝ᵥ x = v ⬝ᵥ F x then (1 : ℤ) else 0) - 1 := by
    intro x
    by_cases hx : u ⬝ᵥ x = v ⬝ᵥ F x
    · rw [if_pos (zmod2_add_eq_zero_iff.mpr hx), if_pos hx]; norm_num
    · rw [if_neg (fun h => hx (zmod2_add_eq_zero_iff.mp h)), if_neg hx]; norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, card_vec, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

theorem walsh_zero_zero (F : Vec ι → Vec κ) : walsh F 0 0 = 2 ^ Fintype.card ι := by
  simp only [walsh_eq_sum_chi_mul, chi_zero_left, mul_one, Finset.sum_const, Finset.card_univ,
    card_vec, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- `W_F(u, 0) = 0` for `u ≠ 0`: a nonzero mask is balanced on the input. -/
theorem walsh_zero_right (F : Vec ι → Vec κ) {u : Vec ι} (hu : u ≠ 0) : walsh F u 0 = 0 := by
  rw [walsh_eq_sum_chi_mul]
  simp only [chi_zero_left, mul_one]
  rw [sum_chi, if_neg hu]

/-- A permutation is balanced: `W_F(0, v) = 0` for `v ≠ 0`. -/
theorem walsh_zero_left_of_bijective {F : Vec ι → Vec κ} (hF : Function.Bijective F) {v : Vec κ}
    (hv : v ≠ 0) : walsh F 0 v = 0 := by
  classical
  rw [walsh_eq_sum_chi_mul]
  simp only [chi_zero_left, one_mul]
  have h := Equiv.sum_comp (Equiv.ofBijective F hF) (fun y => chi ℤ v y)
  simp only [Equiv.ofBijective_apply] at h
  rw [h, sum_chi, if_neg hv]

/-- Parseval: `Σ_u W_F(u, v)² = 2^{2n}` for every output mask `v`. -/
theorem sum_walsh_sq (F : Vec ι → Vec κ) (v : Vec κ) :
    ∑ u, walsh F u v ^ 2 = 2 ^ (2 * Fintype.card ι) := by
  have key : ∀ u : Vec ι, walsh F u v ^ 2 =
      ∑ x, ∑ y, chi ℤ u (x + y) * (chi ℤ v (F x) * chi ℤ v (F y)) := by
    intro u
    rw [walsh_eq_sum_chi_mul, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [chi_add_right]; ring
  have inner : ∀ x y : Vec ι, ∑ u : Vec ι, chi ℤ u (x + y) * (chi ℤ v (F x) * chi ℤ v (F y)) =
      if x = y then (2 ^ Fintype.card ι : ℤ) else 0 := by
    intro x y
    rw [← Finset.sum_mul]
    have hs : ∑ u : Vec ι, chi ℤ u (x + y) = ∑ u : Vec ι, chi ℤ (x + y) u :=
      Finset.sum_congr rfl fun u _ => chi_comm ℤ u (x + y)
    rw [hs, sum_chi]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos (add_self x), if_pos rfl, chi_mul_self, mul_one]
    · rw [if_neg (fun h => hxy (add_eq_zero_iff.mp h)), if_neg hxy, zero_mul]
  calc ∑ u, walsh F u v ^ 2
      = ∑ u, ∑ x, ∑ y, chi ℤ u (x + y) * (chi ℤ v (F x) * chi ℤ v (F y)) := by
        simp only [key]
    _ = ∑ x, ∑ y, ∑ u, chi ℤ u (x + y) * (chi ℤ v (F x) * chi ℤ v (F y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x : Vec ι, ∑ y : Vec ι, if x = y then (2 ^ Fintype.card ι : ℤ) else 0 := by
        simp only [inner]
    _ = ∑ _x : Vec ι, (2 ^ Fintype.card ι : ℤ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_ite_eq]
    _ = 2 ^ (2 * Fintype.card ι) := by
        rw [Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat, two_mul, pow_add]

theorem correlation_zero_zero (F : Vec ι → Vec κ) : correlation F 0 0 = 1 := by
  rw [correlation, walsh_zero_zero]
  have : (2 : ℚ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  exact div_self this

/-! ## The halfspace identity: a linear sum is twice an integral sum

H. Hadipour, *Connecting Cryptanalytic Distinguishers through Divisibility*, ePrint 2026/2471: for a
permutation `E` and the mask `e = e_{i₀}` on both sides, `W_E(e, e) = 2 · I_0`, where `I_b` is the
integral sum of output bit `i₀` over the halfspace `x i₀ = b`. Promoted from
`Examples/Halfspace`. -/

/-- `I_b(E; i₀) = Σ_{x : x i₀ = b} (-1)^{E(x) i₀}`, the unnormalized integral sum of output bit `i₀`
over the halfspace `x i₀ = b`. -/
def halfSum (E : Vec ι → Vec ι) (i₀ : ι) (b : ZMod 2) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x : Vec ι => x i₀ = b), sgn ℤ ((E x) i₀)

/-- Step 1 (no hypothesis on `E`): `W_E(e_{i₀}, e_{i₀}) = I_0 − I_1`, by splitting the sum over the
two halfspaces. -/
theorem walsh_single_eq_sub (E : Vec ι → Vec ι) (i₀ : ι) :
    walsh E (Pi.single i₀ 1) (Pi.single i₀ 1) = halfSum E i₀ 0 - halfSum E i₀ 1 := by
  unfold walsh halfSum
  simp only [single_dot]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Vec ι => x i₀ = 0)]
  have h0 : ∑ x ∈ Finset.univ.filter (fun x : Vec ι => x i₀ = 0), sgn ℤ (x i₀ + (E x) i₀) =
      ∑ x ∈ Finset.univ.filter (fun x : Vec ι => x i₀ = 0), sgn ℤ ((E x) i₀) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2, zero_add]
  have h1 : ∑ x ∈ Finset.univ.filter (fun x : Vec ι => ¬ x i₀ = 0), sgn ℤ (x i₀ + (E x) i₀) =
      - ∑ x ∈ Finset.univ.filter (fun x : Vec ι => x i₀ = 1), sgn ℤ ((E x) i₀) := by
    rw [filter_ne_zero_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2, sgn_add, sgn_one, neg_one_mul]
  rw [h0, h1, sub_eq_add_neg]

/-- Step 2 (uses that `E` is a permutation): the selected output bit is balanced over the whole
space, so `I_0 + I_1 = 0`. -/
theorem halfSum_add_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) :
    halfSum E i₀ 0 + halfSum E i₀ 1 = 0 := by
  unfold halfSum
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Vec ι => x i₀ = 0)
    (fun x => sgn ℤ ((E x) i₀))
  rw [filter_ne_zero_eq] at hsplit
  rw [hsplit]
  have hre := Equiv.sum_comp (Equiv.ofBijective E hE) (fun y : Vec ι => sgn ℤ (y i₀))
  simp only [Equiv.ofBijective_apply] at hre
  rw [hre]
  have hchi : ∀ y : Vec ι, sgn ℤ (y i₀) = chi ℤ (Pi.single i₀ 1) y := fun y => by
    rw [chi, single_dot]
  simp only [hchi]
  rw [sum_chi, if_neg]
  intro h
  have := congrFun h i₀
  simp at this

/-- The halfspace identity: `W_E(e_{i₀}, e_{i₀}) = 2 · I_0` for every permutation `E`. -/
theorem walsh_single_eq_two_mul_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E)
    (i₀ : ι) : walsh E (Pi.single i₀ 1) (Pi.single i₀ 1) = 2 * halfSum E i₀ 0 := by
  have h1 := walsh_single_eq_sub E i₀
  have h2 := halfSum_add_halfSum E hE i₀
  linarith

/-- Divisibility transfer: `2^(t+1) ∣ W_E(e, e)` implies `2^t ∣ I_0`. -/
theorem pow_dvd_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) (t : ℕ)
    (h : (2 : ℤ) ^ (t + 1) ∣ walsh E (Pi.single i₀ 1) (Pi.single i₀ 1)) :
    (2 : ℤ) ^ t ∣ halfSum E i₀ 0 := by
  rw [walsh_single_eq_two_mul_halfSum E hE, pow_succ'] at h
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h

/-! ## Finite checks on the PRESENT S-box -/

section toy
open Sbox

/-- Two Walsh coefficients of the PRESENT S-box (masks written as words through `toVec`):
`W(e₀, e₀ + e₂) = -8` and `#{x : x₀ = S(x)₀} = 8`, i.e. `W(e₀, e₀) = 0`. Values computed by
`decide`, matching an independent Python computation. -/
theorem present_walsh_values :
    walsh presentVec (toVec (1 : BitVec 4)) (toVec (5 : BitVec 4)) = -8 ∧
      linCount presentVec (toVec (1 : BitVec 4)) (toVec (1 : BitVec 4)) = 8 := by
  decide +kernel

theorem present_walsh_zero_zero : walsh presentVec 0 0 = 16 := by
  rw [walsh_zero_zero]; rfl

end toy

end CipherLean
