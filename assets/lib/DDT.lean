import CipherLean.Lib.Sbox
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.SplitIfs

/-!
# `CipherLean.Lib.DDT` — difference distribution table and differential uniformity

`ddt F a b = #{x : F(x + a) + F(x) = b}` is the DDT entry of `F : F_2^ι → F_2^κ` at input
difference `a` and output difference `b`, an unnormalized count (the differential probability is
`ddt / 2^n`). `diffUniformity F = max_{a ≠ 0, b} ddt F a b` is Nyberg's differential uniformity
(K. Nyberg, *Differentially Uniform Mappings for Cryptography*, EUROCRYPT 1993).
-/

namespace CipherLean

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- DDT entry: the number of inputs `x` with `F (x + a) + F x = b`. -/
def ddt (F : Vec ι → Vec κ) (a : Vec ι) (b : Vec κ) : ℕ :=
  (Finset.univ.filter fun x => F (x + a) + F x = b).card

/-- Every row of the DDT sums to `2^n`: the inputs are partitioned by their output difference. -/
theorem ddt_row_sum (F : Vec ι → Vec κ) (a : Vec ι) : ∑ b, ddt F a b = 2 ^ Fintype.card ι := by
  unfold ddt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (F (x + a) + F x))]
  rw [Finset.card_univ, card_vec]

omit [DecidableEq κ] in
/-- The zero row: `ddt F 0 b` is `2^n` for `b = 0` and `0` otherwise. -/
theorem ddt_zero_left (F : Vec ι → Vec κ) (b : Vec κ) :
    ddt F 0 b = if b = 0 then 2 ^ Fintype.card ι else 0 := by
  unfold ddt
  simp only [add_zero, add_self]
  split_ifs with hb
  · subst hb
    simp [Finset.card_univ]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ h
    exact hb h.symm

omit [DecidableEq κ] in
/-- The DDT entry does not depend on which of `x`, `x + a` is counted (`ddt F a b` is even for
`a ≠ 0`): the involution `x ↦ x + a` has no fixed point and preserves the counted set. -/
theorem even_ddt (F : Vec ι → Vec κ) {a : Vec ι} (ha : a ≠ 0) (b : Vec κ) : Even (ddt F a b) := by
  unfold ddt
  set s := Finset.univ.filter fun x => F (x + a) + F x = b with hs
  have hsum : ∑ _x ∈ s, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun x _ => x + a) ?_ ?_ ?_ ?_
    · intro x _; exact zmod2_one_add_one
    · intro x _ _ h
      exact ha (add_eq_left.mp h)
    · intro x hx
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [add_add_self, add_comm]; exact hx
    · intro x _; exact add_add_self x a
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

omit [Fintype ι] [DecidableEq ι] in
/-- Step of the inverse-symmetry proof: if `x` is counted in `ddt F a b`, then `F x` is counted in
`ddt G b a` for any left inverse `G` of `F`. -/
theorem image_cond {F G : Vec ι → Vec ι} (hGF : ∀ x, G (F x) = x) {a b x : Vec ι}
    (h : F (x + a) + F x = b) : G (F x + b) + G (F x) = a := by
  subst h
  have h1 : F x + (F (x + a) + F x) = F (x + a) := by
    rw [add_comm (F (x + a)), ← add_assoc, add_self, zero_add]
  rw [h1, hGF, hGF, add_comm x a, add_assoc, add_self, add_zero]

/-- `ddt F a b = ddt G b a` for mutually inverse `F`, `G` (the DDT of the inverse is the
transpose). -/
theorem ddt_eq_ddt_of_inverse (F G : Vec ι → Vec ι) (hGF : ∀ x, G (F x) = x)
    (hFG : ∀ y, F (G y) = y) (a b : Vec ι) : ddt F a b = ddt G b a := by
  unfold ddt
  refine Finset.card_nbij' F G ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact image_cond hGF hx
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact image_cond hFG hy
  · intro x _
    exact hGF x
  · intro y _
    exact hFG y

/-- The DDT of a permutation's inverse is the transpose of its DDT. -/
theorem ddt_symm (F : Equiv.Perm (Vec ι)) (a b : Vec ι) : ddt F a b = ddt F.symm b a :=
  ddt_eq_ddt_of_inverse F F.symm F.symm_apply_apply F.apply_symm_apply a b

/-- Differential uniformity `δ(F) = max_{a ≠ 0, b} ddt F a b` (Nyberg, EUROCRYPT 1993). -/
def diffUniformity (F : Vec ι → Vec κ) : ℕ :=
  (Finset.univ.filter fun a : Vec ι => a ≠ 0).sup fun a => Finset.univ.sup fun b => ddt F a b

theorem ddt_le_diffUniformity (F : Vec ι → Vec κ) {a : Vec ι} (ha : a ≠ 0) (b : Vec κ) :
    ddt F a b ≤ diffUniformity F := by
  unfold diffUniformity
  have h1 : ddt F a b ≤ Finset.univ.sup fun b => ddt F a b :=
    Finset.le_sup (f := fun b => ddt F a b) (Finset.mem_univ b)
  have h2 : (Finset.univ.sup fun b => ddt F a b) ≤
      (Finset.univ.filter fun a : Vec ι => a ≠ 0).sup fun a => Finset.univ.sup fun b => ddt F a b :=
    Finset.le_sup (f := fun a => Finset.univ.sup fun b => ddt F a b) (by simp [ha])
  exact le_trans h1 h2

theorem diffUniformity_le_iff (F : Vec ι → Vec κ) {d : ℕ} :
    diffUniformity F ≤ d ↔ ∀ a : Vec ι, a ≠ 0 → ∀ b, ddt F a b ≤ d := by
  unfold diffUniformity
  simp [Finset.sup_le_iff]

/-- `F` is almost perfect nonlinear (APN) when `δ(F) = 2`, the smallest possible value. -/
def IsAPN (F : Vec ι → Vec κ) : Prop := diffUniformity F = 2

/-! ## Computing on words: the DDT of a table S-box through the bridge -/

section bridge
variable {n : ℕ}
open Sbox

/-- The DDT of a table S-box, as a count over words: `ddt (toFun S) (toVec a) (toVec b)` is
`#{x : S (x ^^^ a) ^^^ S x = b}`. This is what `decide` evaluates quickly. -/
theorem ddt_toFun (S : BitVec n → BitVec n) (a b : BitVec n) :
    ddt (toFun S) (toVec a) (toVec b) =
      (Finset.univ.filter fun x : BitVec n => S (x ^^^ a) ^^^ S x = b).card := by
  unfold ddt
  symm
  refine Finset.card_nbij' toVec ofVec ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← toVec_xor, toFun_toVec, toFun_toVec, ← toVec_xor, hx]
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    apply toVec_injective
    rw [toVec_xor, ← hv, toFun_apply, toFun_apply, ofVec_add, ofVec_toVec]
  · intro x _
    exact ofVec_toVec x
  · intro v _
    exact toVec_ofVec v

/-- Differential uniformity of a table S-box, decided on words. -/
theorem diffUniformity_toFun_le_iff (S : BitVec n → BitVec n) {d : ℕ} :
    diffUniformity (toFun S) ≤ d ↔
      ∀ a : BitVec n, a ≠ 0 → ∀ b : BitVec n,
        (Finset.univ.filter fun x : BitVec n => S (x ^^^ a) ^^^ S x = b).card ≤ d := by
  rw [diffUniformity_le_iff]
  constructor
  · intro h a ha b
    rw [← ddt_toFun]
    exact h (toVec a) (fun h0 => ha (toVec_injective (by rw [h0, toVec_zero]))) (toVec b)
  · intro h a ha b
    obtain ⟨a', rfl⟩ := bvEquiv.surjective a
    obtain ⟨b', rfl⟩ := bvEquiv.surjective b
    simp only [bvEquiv_apply] at ha ⊢
    rw [ddt_toFun]
    exact h a' (fun h0 => ha (by rw [h0, toVec_zero])) b'

end bridge

/-! ## Finite checks on the PRESENT S-box (computed on words through the bridge) -/

section toy
open Sbox

/-- The PRESENT S-box has differential uniformity exactly `4`: every off-row entry is `≤ 4`
(decided on words) and the entry at `(a, b) = (1, 3)` equals `4`. -/
theorem present_diffUniformity : diffUniformity presentVec = 4 := by
  unfold presentVec
  apply le_antisymm
  · exact (diffUniformity_toFun_le_iff present).mpr (by decide +kernel)
  · have h := ddt_le_diffUniformity (toFun present) (a := toVec (1 : BitVec 4))
      (fun h0 => by have := congrFun h0 0; simp [toVec_apply] at this) (toVec (3 : BitVec 4))
    rw [ddt_toFun] at h
    have h4 : (Finset.univ.filter fun x : BitVec 4 =>
        present (x ^^^ 1) ^^^ present x = 3).card = 4 := by
      decide +kernel
    omega

/-- The zero row of the PRESENT DDT, and one entry of a 3-bit toy, through the general lemmas. -/
theorem present_ddt_zero : ddt presentVec 0 0 = 16 := by
  rw [ddt_zero_left, if_pos rfl]; rfl

end toy

end CipherLean
