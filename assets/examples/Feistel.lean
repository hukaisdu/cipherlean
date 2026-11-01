/-!
# Example 0: one Feistel round is invertible for every round function

No Mathlib needed: `BitVec`, its xor lemmas and `Function.LeftInverse` are in core Lean. This is the warm-up of
Hadipour's "Lean for Cryptanalysts" (2026), re-typed.

Statement: for every word size `n`, every `F : BitVec n → BitVec n` (not necessarily
bijective) and every input `(l, r)`, the round `(l, r) ↦ (r, l ^^^ F r)` is undone by
`(a, b) ↦ (b ^^^ F a, a)`.
-/

namespace Feistel

/-- One Feistel round: swap, and xor the round function of the right half into the left. -/
def round {n : Nat} (F : BitVec n → BitVec n) (x : BitVec n × BitVec n) : BitVec n × BitVec n :=
  (x.2, x.1 ^^^ F x.2)

/-- The candidate inverse. -/
def roundInv {n : Nat} (F : BitVec n → BitVec n) (y : BitVec n × BitVec n) : BitVec n × BitVec n :=
  (y.2 ^^^ F y.1, y.1)

/-- `roundInv` undoes `round`, for every `F`. The proof is `(l ^^^ F r) ^^^ F r = l`. -/
theorem roundInv_round {n : Nat} (F : BitVec n → BitVec n) (l r : BitVec n) :
    roundInv F (round F (l, r)) = (l, r) := by
  simp [round, roundInv, BitVec.xor_assoc]

/-- And `round` undoes `roundInv`. -/
theorem round_roundInv {n : Nat} (F : BitVec n → BitVec n) (a b : BitVec n) :
    round F (roundInv F (a, b)) = (a, b) := by
  simp [round, roundInv, BitVec.xor_assoc]

/-- `roundInv` is a two-sided inverse of `round`. With Mathlib, `Function.bijective_iff_has_inverse`
turns this pair into `Function.Bijective (round F)`; core Lean has no `Bijective`, so the pair is
the statement here. -/
theorem roundInv_leftInverse {n : Nat} (F : BitVec n → BitVec n) :
    Function.LeftInverse (roundInv F) (round F) :=
  fun ⟨l, r⟩ => roundInv_round F l r

theorem roundInv_rightInverse {n : Nat} (F : BitVec n → BitVec n) :
    Function.RightInverse (roundInv F) (round F) :=
  fun ⟨a, b⟩ => round_roundInv F a b

/-- Finite check on 4-bit words with a non-bijective round function. -/
def toyF (r : BitVec 4) : BitVec 4 := r &&& 3

theorem toy_check : ∀ l r : BitVec 4, roundInv toyF (round toyF (l, r)) = (l, r) := by
  decide

end Feistel

#print axioms Feistel.roundInv_leftInverse
