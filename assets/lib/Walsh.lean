import CipherLean.Lib.Sbox
import Mathlib.Algebra.Ring.IsFormallyReal
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
