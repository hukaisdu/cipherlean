/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# `CipherLean.Lib.F2.Vec` — the carrier `F_2^ι`, signs, characters, and the `BitVec` bridge

Library convention (fixed 2026-11-01): every cryptanalysis statement is made over
`Vec ι := ι → ZMod 2` for a finite index type `ι` (`Fin n` for an `n`-bit word, a product index
for a state split into words). Vector addition is bitwise xor, `u ⬝ᵥ x` is the `F_2` dot product
(a mask applied to a value), and `chi K u x = (-1)^{u·x}` is the character with values in a
commutative ring `K` (`ℤ` for statistics, `ℚ` or `ℝ` for normalized quantities). Concrete tables
live on `BitVec n`; `bvEquiv : BitVec n ≃ Vec (Fin n)` is the bridge, and `toVec_xor` turns xor
into addition.

Definitions follow C. Carlet, *Boolean Functions for Cryptography and Coding Theory*, Cambridge
University Press 2021, §2.2 (characters, Walsh transform), restated for vectorial functions.
-/

namespace CipherLean

/-- `F_2^ι`: vectors over `F_2` indexed by the finite type `ι`. Addition is bitwise xor. -/
abbrev Vec (ι : Type*) := ι → ZMod 2

/-! ## Facts about `F_2` used everywhere -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem zmod2_add_eq_zero_iff {a b : ZMod 2} : a + b = 0 ↔ a = b := by revert a b; decide

theorem zmod2_ne_zero_iff {a : ZMod 2} : a ≠ 0 ↔ a = 1 := by revert a; decide

/-- `(p + q) + (q + r) = p + r` in `F_2`. -/
theorem zmod2_add_add_add (p q r : ZMod 2) : p + q + (q + r) = p + r := by
  revert p q r; decide

section basic
variable {ι : Type*}

theorem add_self (x : Vec ι) : x + x = 0 := funext fun i => CharTwo.add_self_eq_zero (x i)

theorem add_add_self (x k : Vec ι) : x + k + k = x := by rw [add_assoc, add_self, add_zero]

theorem neg_eq (x : Vec ι) : -x = x := funext fun i => CharTwo.neg_eq (x i)

theorem add_eq_zero_iff {x y : Vec ι} : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (· + y) h
    simpa only [add_add_self, zero_add] using h'
  · rintro rfl
    exact add_self x

/-- Over `F_2`, `u + v = w ↔ u = w + v` (adding `v` to both sides). -/
theorem add_eq_iff_eq_add {u v w : Vec ι} : u + v = w ↔ u = w + v := by
  constructor
  · intro h
    rw [← h, add_add_self]
  · intro h
    rw [h, add_add_self]

/-- Gluing two words: `Sum.elim A B = f` iff `A` and `B` are the two restrictions of `f`
(not in Mathlib, which has only `Sum.elim_comp_inl_inr`). -/
theorem sum_elim_eq_iff {κ : Type*} {f : Vec (ι ⊕ κ)} {A : Vec ι} {B : Vec κ} :
    Sum.elim A B = f ↔ A = f ∘ Sum.inl ∧ B = f ∘ Sum.inr := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Sum.elim_comp_inl_inr f

/-- A nonzero vector has a coordinate equal to `1`. -/
theorem exists_eq_one_of_ne_zero {w : Vec ι} (hw : w ≠ 0) : ∃ i, w i = 1 := by
  by_contra h
  simp only [not_exists] at h
  exact hw (funext fun i => (zmod2_cases (w i)).resolve_right (h i))

end basic

variable {ι : Type*} [Fintype ι]

/-- `|F_2^ι| = 2^{|ι|}`. -/
theorem card_vec [DecidableEq ι] : Fintype.card (Vec ι) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, ZMod.card]

/-- The mask selecting coordinate `i₀`, applied to `x`, is the coordinate `x i₀`. -/
theorem single_dot [DecidableEq ι] (i₀ : ι) (x : Vec ι) : (Pi.single i₀ 1 : Vec ι) ⬝ᵥ x = x i₀ := by
  rw [single_dotProduct, one_mul]

/-- The complement of the halfspace `x i₀ = 0` is the halfspace `x i₀ = 1`. -/
theorem filter_ne_zero_eq [DecidableEq ι] (i₀ : ι) :
    Finset.univ.filter (fun x : Vec ι => ¬ x i₀ = 0) =
      Finset.univ.filter (fun x : Vec ι => x i₀ = 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact zmod2_ne_zero_iff

/-- The dot product on `F_2^ι × F_2^κ` (a vector indexed by `ι ⊕ κ`, two words) splits along the
two words: `⟨λ, (A ‖ B)⟩ = ⟨λ_L, A⟩ + ⟨λ_R, B⟩` (companion of `sum_elim_eq_iff`; promoted from
`WHConj3`, 2026-11-02). -/
theorem dot_sum_elim {κ : Type*} [Fintype κ] (lam : Vec (ι ⊕ κ)) (A : Vec ι) (B : Vec κ) :
    lam ⬝ᵥ Sum.elim A B = (lam ∘ Sum.inl) ⬝ᵥ A + (lam ∘ Sum.inr) ⬝ᵥ B := by
  simp [dotProduct, Fintype.sum_sum_type]

/-! ## Signs and characters -/

section sgn
variable (K : Type*) [CommRing K]

/-- `(-1)^a` for `a ∈ F_2`, as an element of `K`. -/
def sgn (a : ZMod 2) : K := if a = 0 then 1 else -1

@[simp] theorem sgn_zero : sgn K 0 = 1 := by simp [sgn]

@[simp] theorem sgn_one : sgn K 1 = -1 := by simp [sgn]

/-- Signs multiply: `(-1)^{a+b} = (-1)^a (-1)^b`. -/
theorem sgn_add (a b : ZMod 2) : sgn K (a + b) = sgn K a * sgn K b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [zmod2_one_add_one]

theorem sgn_mul_self (a : ZMod 2) : sgn K a * sgn K a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

theorem sgn_sq (a : ZMod 2) : sgn K a ^ 2 = 1 := by rw [sq, sgn_mul_self]

theorem sgn_ne_zero [Nontrivial K] (a : ZMod 2) : sgn K a ≠ 0 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

/-- The character `χ_w(x) = (-1)^{w·x}` of `F_2^ι`, with values in `K`. -/
def chi (w x : Vec ι) : K := sgn K (w ⬝ᵥ x)

theorem chi_add_left (w₁ w₂ x : Vec ι) : chi K (w₁ + w₂) x = chi K w₁ x * chi K w₂ x := by
  unfold chi; rw [add_dotProduct]; exact sgn_add K _ _

theorem chi_add_right (w x k : Vec ι) : chi K w (x + k) = chi K w x * chi K w k := by
  unfold chi; rw [dotProduct_add]; exact sgn_add K _ _

@[simp] theorem chi_zero_left (x : Vec ι) : chi K 0 x = 1 := by simp [chi]

@[simp] theorem chi_zero_right (w : Vec ι) : chi K w 0 = 1 := by simp [chi]

theorem chi_comm (w x : Vec ι) : chi K w x = chi K x w := by unfold chi; rw [dotProduct_comm]

theorem chi_eq_one {w x : Vec ι} (h : w ⬝ᵥ x = 0) : chi K w x = 1 := by simp [chi, h]

theorem chi_eq_neg_one {w x : Vec ι} (h : w ⬝ᵥ x ≠ 0) : chi K w x = -1 := by
  simp [chi, sgn, h]

theorem chi_mul_self (w x : Vec ι) : chi K w x * chi K w x = 1 := sgn_mul_self K _

/-- Orthogonality of characters: `Σ_x χ_w(x)` is `2^n` for `w = 0` and `0` otherwise
(pair `x` with `x + x₀` where `w·x₀ = 1`). -/
theorem sum_chi [DecidableEq ι] (w : Vec ι) :
    ∑ x, chi K w x = if w = 0 then (2 ^ Fintype.card ι : K) else 0 := by
  split_ifs with hw
  · subst hw
    simp only [chi_zero_left, Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul,
      mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · obtain ⟨i, hi⟩ := exists_eq_one_of_ne_zero hw
    have hx₀ : w ⬝ᵥ Pi.single i (1 : ZMod 2) ≠ 0 := by
      rw [dotProduct_single, hi, one_mul]; exact one_ne_zero
    refine Finset.sum_involution (fun x _ => x + Pi.single i 1) ?_ ?_ ?_ ?_
    · intro x _
      rw [chi_add_right, chi_eq_neg_one K hx₀]; ring
    · intro x _ _ h
      have h0 : (Pi.single i 1 : Vec ι) = 0 := add_eq_left.mp h
      exact hx₀ (by rw [h0, dotProduct_zero])
    · intro x _
      exact Finset.mem_univ _
    · intro x _
      exact add_add_self x _

/-- A sum of `2^n` signs `±1` equals `2^n` iff every sign is `+1`, and `−2^n` iff every sign is
`−1` (the "absolute bias one" criterion). -/
theorem sum_sgn_eq_iff [DecidableEq ι] (s : Vec ι → ZMod 2) :
    ((∑ y, sgn ℤ (s y)) = 2 ^ Fintype.card ι ↔ ∀ y, s y = 0) ∧
      ((∑ y, sgn ℤ (s y)) = -(2 ^ Fintype.card ι) ↔ ∀ y, s y = 1) := by
  classical
  have hsum : (∑ y, sgn ℤ (s y)) =
      ((Finset.univ.filter fun y : Vec ι => s y = 0).card : ℤ) -
        ((Finset.univ.filter fun y : Vec ι => ¬ s y = 0).card : ℤ) := by
    simp only [sgn]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
      mul_neg, mul_one, sub_eq_add_neg]
  have hcardN : (Finset.univ.filter fun y : Vec ι => s y = 0).card +
      (Finset.univ.filter fun y : Vec ι => ¬ s y = 0).card = 2 ^ Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, card_vec]
  have hcard : ((Finset.univ.filter fun y : Vec ι => s y = 0).card : ℤ) +
      ((Finset.univ.filter fun y : Vec ι => ¬ s y = 0).card : ℤ) = 2 ^ Fintype.card ι := by
    exact_mod_cast hcardN
  have hB : (Finset.univ.filter fun y : Vec ι => ¬ s y = 0).card = 0 ↔ ∀ y, s y = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp
  have hA : (Finset.univ.filter fun y : Vec ι => s y = 0).card = 0 ↔ ∀ y, s y = 1 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp [zmod2_ne_zero_iff]
  rw [hsum]
  constructor
  · rw [← hB]
    constructor <;> intro h <;> omega
  · rw [← hA]
    constructor <;> intro h <;> omega

end sgn

/-! ## The bridge to `BitVec n` (concrete words and tables) -/

section bridge
variable {n : ℕ}

/-- An `n`-bit word as a vector: coordinate `i` is bit `i`, least significant bit first. -/
def toVec (x : BitVec n) : Vec (Fin n) := fun i => if x.getLsbD i then 1 else 0

/-- The inverse of `toVec`, built from the most significant bit down. -/
def ofVec : {n : ℕ} → Vec (Fin n) → BitVec n
  | 0, _ => 0#0
  | n + 1, v => BitVec.cons (decide (v (Fin.last n) = 1)) (ofVec fun i => v i.castSucc)

theorem toVec_apply (x : BitVec n) (i : Fin n) : toVec x i = if x.getLsbD i then 1 else 0 := rfl

theorem toVec_injective : Function.Injective (toVec (n := n)) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hxy := congrFun h ⟨i, hi⟩
  simp only [toVec_apply] at hxy
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem toVec_ofVec : ∀ {n : ℕ} (v : Vec (Fin n)), toVec (ofVec v) = v
  | 0, v => funext fun i => i.elim0
  | n + 1, v => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [toVec_apply, ofVec, BitVec.getLsbD_cons, Fin.val_last, if_true]
      rcases zmod2_cases (v (Fin.last n)) with h | h <;> simp [h]
    · simp only [toVec_apply, ofVec, BitVec.getLsbD_cons, Fin.val_castSucc]
      rw [if_neg (Nat.ne_of_lt j.isLt)]
      exact congrFun (toVec_ofVec (fun i => v i.castSucc)) j

theorem ofVec_toVec (x : BitVec n) : ofVec (toVec x) = x :=
  toVec_injective (toVec_ofVec (toVec x))

/-- Words of `n` bits and vectors in `F_2^n` are the same thing; `toVec_xor` says the bridge
turns xor into addition. -/
def bvEquiv : BitVec n ≃ Vec (Fin n) where
  toFun := toVec
  invFun := ofVec
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec

@[simp] theorem bvEquiv_apply (x : BitVec n) : bvEquiv x = toVec x := rfl

@[simp] theorem bvEquiv_symm_apply (v : Vec (Fin n)) : bvEquiv.symm v = ofVec v := rfl

theorem toVec_xor (x y : BitVec n) : toVec (x ^^^ y) = toVec x + toVec y := by
  funext i
  simp only [toVec_apply, Pi.add_apply, BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> simp [zmod2_one_add_one]

@[simp] theorem toVec_zero : toVec (0 : BitVec n) = 0 := by
  funext i; simp [toVec_apply]

theorem ofVec_add (v w : Vec (Fin n)) : ofVec (v + w) = ofVec v ^^^ ofVec w :=
  toVec_injective (by rw [toVec_xor, toVec_ofVec, toVec_ofVec, toVec_ofVec])

/-- `|BitVec n| = 2^n`. -/
theorem card_bitVec : Fintype.card (BitVec n) = 2 ^ n := by
  rw [Fintype.card_congr bvEquiv, card_vec, Fintype.card_fin]

end bridge

end CipherLean
