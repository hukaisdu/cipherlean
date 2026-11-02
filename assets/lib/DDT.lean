/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.Sbox
import CipherLean.Lib.F2.Affine
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Fin.VecNotation

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

/-- The same lemma for a bijective function, with `F⁻¹ = Function.invFun F`. -/
theorem ddt_invFun (F : Vec ι → Vec ι) (hF : Function.Bijective F) (a b : Vec ι) :
    ddt F a b = ddt (Function.invFun F) b a :=
  ddt_eq_ddt_of_inverse F (Function.invFun F) (Function.leftInverse_invFun hF.1)
    (Function.rightInverse_invFun hF.2) a b

/-- On a finite type one inverse equation suffices: `G ∘ F = id` alone makes `F` a permutation and
`G` its two-sided inverse. -/
theorem ddt_eq_ddt_of_leftInverse (F G : Vec ι → Vec ι) (hGF : ∀ x, G (F x) = x) (a b : Vec ι) :
    ddt F a b = ddt G b a :=
  ddt_eq_ddt_of_inverse F G hGF
    ((Function.LeftInverse.rightInverse_of_surjective hGF)
      (Finite.injective_iff_surjective.mp (Function.LeftInverse.injective hGF))) a b

/-- The DDT as a table: rows indexed by the input difference, columns by the output difference. -/
def ddtMatrix (F : Vec ι → Vec κ) : Matrix (Vec ι) (Vec κ) ℕ :=
  Matrix.of fun a b => ddt F a b

/-- The DDT of a permutation's inverse is the transpose of its DDT, as matrices. -/
theorem ddtMatrix_symm (F : Equiv.Perm (Vec ι)) :
    ddtMatrix F.symm = (ddtMatrix F).transpose := by
  ext a b
  simp only [ddtMatrix, Matrix.of_apply, Matrix.transpose_apply]
  exact (ddt_symm F b a).symm

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

/-- Every DDT row of an `n`-bit table S-box sums to `2^n`. -/
theorem ddt_toFun_row_sum (S : BitVec n → BitVec n) (a : Vec (Fin n)) :
    ∑ b, ddt (toFun S) a b = 2 ^ n := by
  rw [ddt_row_sum, Fintype.card_fin]

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

/-! ## Derivatives and the two difference sets of a map

`deriv F d x = F (x + d) + F x` is the derivative of `F` in direction `d` (Carlet 2021, §2.3.1;
the papers write `Δ_d F(x)`). For an output difference `β`, `inputDiffs F β` is the set of input
differences `d` that attain it, i.e. the support of column `β` of the DDT
(`mem_inputDiffs_iff_ddt_ne_zero`); for an input difference `α`, `outputDiffs H α` is the set of
output differences `H (y + α) + H y`. When `H = F⁻¹`, the output differences of `H` at `α` are the input
differences of `F` that attain `α` (`outputDiffs_inv_eq_inputDiffs`): the "viewpoint table" of the
ChiChi paper (§2.1), by which a statement about an inverse is read on the forward map. First used by
`WHConj3` (§6.1 of that paper). -/

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The derivative `Δ_d F(x) = F(x + d) + F(x)` of a vectorial map. -/
def deriv (F : Vec ι → Vec κ) (d x : Vec ι) : Vec κ := F (x + d) + F x

/-- The input differences of `F` that attain the output difference `β`: `{d : ∃ x, Δ_d F(x) = β}`. -/
def inputDiffs (F : Vec ι → Vec κ) (β : Vec κ) : Finset (Vec ι) :=
  Finset.univ.filter (fun d => ∃ x, deriv F d x = β)

/-- The output differences of `H` at the input difference `α`: `{H (y + α) + H y : y}`. -/
def outputDiffs (H : Vec ι → Vec κ) (α : Vec ι) : Finset (Vec κ) :=
  Finset.univ.image (fun y => deriv H α y)

omit [DecidableEq κ] in
theorem mem_inputDiffs {F : Vec ι → Vec κ} {β : Vec κ} {d : Vec ι} :
    d ∈ inputDiffs F β ↔ ∃ x, deriv F d x = β := by
  simp [inputDiffs]

omit [DecidableEq κ] in
theorem mem_outputDiffs {H : Vec ι → Vec κ} {α : Vec ι} {d : Vec κ} :
    d ∈ outputDiffs H α ↔ ∃ y, deriv H α y = d := by
  simp [outputDiffs]

omit [DecidableEq κ] in
/-- `inputDiffs F β` is the support of column `β` of the DDT. -/
theorem mem_inputDiffs_iff_ddt_ne_zero (F : Vec ι → Vec κ) (d : Vec ι) (β : Vec κ) :
    d ∈ inputDiffs F β ↔ ddt F d β ≠ 0 := by
  rw [mem_inputDiffs, ddt, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [deriv]

/-- For a permutation `F` with inverse `H`, the output differences of `H` at `α` are the input
differences of `F` that attain `α` (the viewpoint table; the argument of Lemma 2 of the ChiChi paper
for one χ cycle, here for any bijection). -/
theorem outputDiffs_inv_eq_inputDiffs {F : Vec ι → Vec ι} (hbij : Function.Bijective F) (α : Vec ι) :
    outputDiffs (Equiv.ofBijective F hbij).symm α = inputDiffs F α := by
  set e := Equiv.ofBijective F hbij with he
  have hF : ∀ z, F z = e z := fun z => rfl
  ext d
  rw [mem_inputDiffs, mem_outputDiffs]
  simp only [deriv]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e.symm y, ?_⟩
    have h1 : e.symm y + (e.symm (y + α) + e.symm y) = e.symm (y + α) := by
      rw [add_comm (e.symm (y + α)), ← add_assoc, add_self, zero_add]
    rw [h1, hF, hF, e.apply_symm_apply, e.apply_symm_apply, add_comm y α, add_add_self]
  · rintro ⟨x, hx⟩
    refine ⟨F x, ?_⟩
    have h1 : F x + α = F (x + d) := by
      rw [← hx, add_comm (F (x + d)) (F x), ← add_assoc, add_self, zero_add]
    rw [h1, hF (x + d), hF x, e.symm_apply_apply, e.symm_apply_apply, add_comm x d, add_add_self]

/-! ## The masks constant on the attainable differences: `K_H(α)`

`KH F α = constMasks (inputDiffs F α)` is the ChiChi paper's `K_H(α) = {λ ∈ F^N : ⟨λ, d⟩ is
constant for d ∈ S_α}` (§2.1 "The four spaces") read on the forward map: `S_α` is
`inputDiffs F α`. The paper's `S_α = {H(y + α) + H(y) : y}` with `H = F⁻¹` gives the same submodule
(`KH_eq_constMasks_outputDiffs`). Membership is decidable, for finite checks. Promoted from
`WHConj3` (Lemma 24, piece B) on 2026-11-02; `KH_eq_orthogonal_dirAff` (the paper's Lemma 1 on this reading) and
`sum_chi_deriv_eq_iff_mem_constMasks` (the differential–linear bias is `±1` iff the mask is constant on `S_α`)
followed from piece C the same day. -/

/-- `K_H(α)`: the masks `λ` with `⟨λ, d⟩` constant over the input differences `d` of `F` that
attain `α` (the ChiChi paper, §2.1), a `ZMod 2`-submodule of `Vec ι`. -/
def KH (F : Vec ι → Vec ι) (α : Vec ι) : Submodule (ZMod 2) (Vec ι) :=
  constMasks (inputDiffs F α)

theorem mem_KH {F : Vec ι → Vec ι} {α lam : Vec ι} :
    lam ∈ KH F α ↔ ∀ d ∈ inputDiffs F α, ∀ d' ∈ inputDiffs F α, lam ⬝ᵥ d = lam ⬝ᵥ d' := Iff.rfl

instance (F : Vec ι → Vec ι) (α lam : Vec ι) : Decidable (lam ∈ KH F α) :=
  decidable_of_iff _ mem_KH.symm

/-- The paper's `K_H(α)` (masks constant on `S_α = {H(y + α) + H(y) : y}`) is `KH F α` when
`H = F⁻¹` (through `outputDiffs_inv_eq_inputDiffs`). -/
theorem KH_eq_constMasks_outputDiffs {F : Vec ι → Vec ι} (hbij : Function.Bijective F)
    (α : Vec ι) : constMasks (outputDiffs (Equiv.ofBijective F hbij).symm α) = KH F α := by
  rw [KH, outputDiffs_inv_eq_inputDiffs]

/-- The ChiChi paper's Lemma 1 on the forward reading: `K_H(α) = dir(D_α)^⊥` with
`S_α = inputDiffs F α` (`constMasks_eq_orthogonal_dirAff` for that set). -/
theorem KH_eq_orthogonal_dirAff (F : Vec ι → Vec ι) (α : Vec ι) :
    KH F α = (dotForm ι).orthogonal (dirAff (inputDiffs F α)) := by
  rw [KH]
  exact constMasks_eq_orthogonal_dirAff _

/-- The differential–linear bias of `H` at `(α, λ)` has absolute value one iff `⟨λ, d⟩` is constant
on the output differences `S_α` (the first paragraph of the proof of the ChiChi paper's Lemma 1);
unnormalized: `∑ y, (−1)^{⟨λ, H(y+α)+H(y)⟩}` is `2^n` or `−2^n`. -/
theorem sum_chi_deriv_eq_iff_mem_constMasks (H : Vec ι → Vec ι) (α lam : Vec ι) :
    ((∑ y, chi ℤ lam (deriv H α y)) = 2 ^ Fintype.card ι ∨
        (∑ y, chi ℤ lam (deriv H α y)) = -(2 ^ Fintype.card ι)) ↔
      lam ∈ constMasks (outputDiffs H α) := by
  have hs := sum_sgn_eq_iff (fun y => lam ⬝ᵥ deriv H α y)
  have e1 : ((∑ y, chi ℤ lam (deriv H α y)) = 2 ^ Fintype.card ι) ↔
      ∀ y, lam ⬝ᵥ deriv H α y = 0 := hs.1
  have e2 : ((∑ y, chi ℤ lam (deriv H α y)) = -(2 ^ Fintype.card ι)) ↔
      ∀ y, lam ⬝ᵥ deriv H α y = 1 := hs.2
  rw [e1, e2, mem_constMasks]
  constructor
  · rintro (h | h) d hd d' hd'
    · obtain ⟨y, rfl⟩ := mem_outputDiffs.mp hd
      obtain ⟨y', rfl⟩ := mem_outputDiffs.mp hd'
      rw [h y, h y']
    · obtain ⟨y, rfl⟩ := mem_outputDiffs.mp hd
      obtain ⟨y', rfl⟩ := mem_outputDiffs.mp hd'
      rw [h y, h y']
  · intro h
    rcases zmod2_cases (lam ⬝ᵥ deriv H α 0) with h0 | h0
    · left
      intro y
      rw [h _ (mem_outputDiffs.mpr ⟨y, rfl⟩) _ (mem_outputDiffs.mpr ⟨0, rfl⟩), h0]
    · right
      intro y
      rw [h _ (mem_outputDiffs.mpr ⟨y, rfl⟩) _ (mem_outputDiffs.mpr ⟨0, rfl⟩), h0]

/-- Finite check: for `F(x) = (x_0 x_1, 0)` on `F_2^2` the input differences attaining `(1, 0)` are
the three nonzero vectors, so only the zero mask is constant on them; for the identity map
`S_α = {α}` and every mask is constant. -/
theorem inputDiffs_quadratic_example :
    inputDiffs (fun x : Vec (Fin 2) => ![x 0 * x 1, 0]) ![1, 0] = {![1, 0], ![0, 1], ![1, 1]} := by
  decide

theorem KH_quadratic_example :
    ∀ lam : Vec (Fin 2), lam ∈ KH (fun x : Vec (Fin 2) => ![x 0 * x 1, 0]) ![1, 0] → lam = 0 := by
  decide +kernel

theorem KH_id_example : ∀ lam : Vec (Fin 2), lam ∈ KH (fun x : Vec (Fin 2) => x) ![1, 0] := by
  decide +kernel

/-- Finite check: for the identity map every direction attains exactly itself. -/
theorem inputDiffs_id_example : inputDiffs (fun x : Vec (Fin 2) => x) ![1, 0] = {![1, 0]} := by
  decide

theorem outputDiffs_id_example : outputDiffs (fun x : Vec (Fin 2) => x) ![1, 0] = {![1, 0]} := by
  decide

end CipherLean
