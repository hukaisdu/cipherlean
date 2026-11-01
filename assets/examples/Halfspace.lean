import Formal.Crypto

/-!
# Example 1: the halfspace identity — a linear sum is twice an integral sum

Source of the statement: H. Hadipour, "Connecting Cryptanalytic Distinguishers through
Divisibility", ePrint 2026/2471, and his blog post "Lean for Cryptanalysts" (2026-10-29).

Stated with the shared library: the state is `Vec ι`, one coordinate `i₀` is selected, the linear
sum is the Walsh coefficient `walsh E e e` for the mask `e = Pi.single i₀ 1` on both sides, and the
integral sum over the halfspace `x i₀ = b` is `halfSum E i₀ b`. For every permutation `E`,

    linearSum E i₀ = 2 * halfSum E i₀ 0.

All sums are integer sums without normalization.
-/

namespace Halfspace

open Crypto

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper: `I_β(X_b; E)`, the unnormalized integral sum of the selected output bit over the
halfspace `x i₀ = b`. -/
def halfSum (E : Vec ι → Vec ι) (i₀ : ι) (b : ZMod 2) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x : Vec ι => x i₀ = b), sgn ℤ ((E x) i₀)

/-- Paper: `L_{α,β}(E)` with both masks selecting coordinate `i₀`: the Walsh coefficient
`W_E(e, e)`, `e = Pi.single i₀ 1`. -/
def linearSum (E : Vec ι → Vec ι) (i₀ : ι) : ℤ :=
  walsh E (Pi.single i₀ 1) (Pi.single i₀ 1)

theorem single_dot (i₀ : ι) (x : Vec ι) : (Pi.single i₀ 1 : Vec ι) ⬝ᵥ x = x i₀ := by
  rw [single_dotProduct, one_mul]

/-- The complement of the halfspace `x i₀ = 0` is the halfspace `x i₀ = 1`. -/
theorem filter_ne_zero_eq (i₀ : ι) :
    Finset.univ.filter (fun x : Vec ι => ¬ x i₀ = 0) =
      Finset.univ.filter (fun x : Vec ι => x i₀ = 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact zmod2_ne_zero_iff

/-- Proof step 1 (no hypothesis on `E`): split the input sum over the two halfspaces. -/
theorem linearSum_eq_sub (E : Vec ι → Vec ι) (i₀ : ι) :
    linearSum E i₀ = halfSum E i₀ 0 - halfSum E i₀ 1 := by
  unfold linearSum walsh halfSum
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

/-- Proof step 2 (uses that `E` is a permutation): every output occurs exactly once, so the
selected output bit is balanced over the whole space. -/
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

/-- Paper: Theorem (linear ↔ integral), for every finite state space and every permutation. -/
theorem linearSum_eq_two_mul_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) :
    linearSum E i₀ = 2 * halfSum E i₀ 0 := by
  have h1 := linearSum_eq_sub E i₀
  have h2 := halfSum_add_halfSum E hE i₀
  linarith

/-- Paper: divisibility transfer, `2^(t+1) ∣ L` implies `2^t ∣ I₀`. -/
theorem pow_dvd_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) (t : ℕ)
    (h : (2 : ℤ) ^ (t + 1) ∣ linearSum E i₀) : (2 : ℤ) ^ t ∣ halfSum E i₀ 0 := by
  rw [linearSum_eq_two_mul_halfSum E hE, pow_succ'] at h
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h

/-- Keyed version: each key selects a permutation; no key enumeration is needed. -/
theorem all_keys {Key : Type} (E : Key → Vec ι → Vec ι) (hE : ∀ K, Function.Bijective (E K))
    (K : Key) (i₀ : ι) : linearSum (E K) i₀ = 2 * halfSum (E K) i₀ 0 :=
  linearSum_eq_two_mul_halfSum (E K) (hE K) i₀

/-! ## Finite checks on `F_2^3`, selected coordinate `0` -/

/-- A 3-bit toy permutation: flip the selected bit exactly when the other two bits are `11`. -/
def toy (x : Vec (Fin 3)) : Vec (Fin 3) :=
  if x 1 = 1 ∧ x 2 = 1 then x + Pi.single 0 1 else x

theorem toy_involutive : Function.Involutive toy := by
  change ∀ x, toy (toy x) = x
  decide +kernel

theorem toy_bijective : Function.Bijective toy := toy_involutive.bijective

/-- The identity holds on the toy: `L = 4 = 2 · I₀`. -/
theorem toy_values : halfSum toy 0 0 = 2 ∧ halfSum toy 0 1 = -2 ∧ linearSum toy 0 = 4 := by
  decide +kernel

/-- Dropping bijectivity breaks the identity: for the constant map, `L = 0` but `I₀ = 4`. -/
def constantMap (_ : Vec (Fin 3)) : Vec (Fin 3) := 0

theorem constantMap_counterexample :
    linearSum constantMap 0 ≠ 2 * halfSum constantMap 0 0 := by
  decide +kernel

end Halfspace

#print axioms Halfspace.linearSum_eq_two_mul_halfSum
#print axioms Halfspace.toy_values
