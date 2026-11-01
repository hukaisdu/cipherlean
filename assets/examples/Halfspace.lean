import CipherLean

/-!
# Example 1: the halfspace identity — a linear sum is twice an integral sum

Source of the statement: H. Hadipour, "Connecting Cryptanalytic Distinguishers through
Divisibility", ePrint 2026/2471, and his blog post "Lean for Cryptanalysts" (2026-10-29).

Stated with the shared library: the state is `Vec ι`, one coordinate `i₀` is selected, the linear
sum is the Walsh coefficient `walsh E e e` for the mask `e = Pi.single i₀ 1` on both sides, and the
integral sum over the halfspace `x i₀ = b` is the library's `halfSum E i₀ b`. The identity itself
was promoted to the library (`CipherLean.walsh_single_eq_two_mul_halfSum`); this file keeps the
paper's names as instances and the finite checks. For every permutation `E`,

    linearSum E i₀ = 2 * halfSum E i₀ 0.

All sums are integer sums without normalization.
-/

namespace Halfspace

open CipherLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper: `L_{α,β}(E)` with both masks selecting coordinate `i₀`: the library's Walsh coefficient
`W_E(e, e)`, `e = Pi.single i₀ 1`. The integral sum `I_β(X_b; E)` is the library's
`halfSum E i₀ b`. -/
def linearSum (E : Vec ι → Vec ι) (i₀ : ι) : ℤ :=
  walsh E (Pi.single i₀ 1) (Pi.single i₀ 1)

/-- Proof step 1 (no hypothesis on `E`): split over the two halfspaces
(`CipherLean.walsh_single_eq_sub`). -/
theorem linearSum_eq_sub (E : Vec ι → Vec ι) (i₀ : ι) :
    linearSum E i₀ = halfSum E i₀ 0 - halfSum E i₀ 1 :=
  walsh_single_eq_sub E i₀

/-- Proof step 2 (uses that `E` is a permutation): the selected output bit is balanced
(`CipherLean.halfSum_add_halfSum`). -/
theorem halfSum_add_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) :
    halfSum E i₀ 0 + halfSum E i₀ 1 = 0 :=
  CipherLean.halfSum_add_halfSum E hE i₀

/-- Paper: Theorem (linear ↔ integral), for every finite state space and every permutation. -/
theorem linearSum_eq_two_mul_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) :
    linearSum E i₀ = 2 * halfSum E i₀ 0 :=
  walsh_single_eq_two_mul_halfSum E hE i₀

/-- Paper: divisibility transfer, `2^(t+1) ∣ L` implies `2^t ∣ I₀`. -/
theorem pow_dvd_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) (t : ℕ)
    (h : (2 : ℤ) ^ (t + 1) ∣ linearSum E i₀) : (2 : ℤ) ^ t ∣ halfSum E i₀ 0 :=
  CipherLean.pow_dvd_halfSum E hE i₀ t h

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
