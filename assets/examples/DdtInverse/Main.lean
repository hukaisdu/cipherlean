import CipherLean

/-!
# DdtInverse: "Lemma (DDT of the inverse S-box)": the DDT of `S⁻¹` is the transpose of that of `S`

Source: the user's statement (2026-11-01, no paper), quoted in `README.md`; names in `NOTATION.md`.
Encodings come from the shared library: `F_2^n` is `CipherLean.Vec ι` (any finite index type), the
DDT entry is `CipherLean.ddt`, and the lemma itself is `CipherLean.ddt_symm` with its engine
`CipherLean.ddt_eq_ddt_of_inverse`. This file states the source's three spellings of `S⁻¹`, the matrix
form, and the finite checks on a 3-bit table, decided on words through the bridge `ddt_toFun`.
-/

namespace DdtInverse

open CipherLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source: "the DDT of S" as a table: rows indexed by the input difference `a`, columns by the
output difference `b`. -/
def ddtMatrix (S : Vec ι → Vec ι) : Matrix (Vec ι) (Vec ι) ℕ :=
  Matrix.of fun a b => ddt S a b

/-- Source: Lemma (DDT of the inverse S-box), "Let S be a permutation of F_2^n and S^{-1} its
inverse. For all a, b: #{x : S(x ⊕ a) ⊕ S(x) = b} = #{y : S^{-1}(y ⊕ b) ⊕ S^{-1}(y) = a}."
Here `S : Equiv.Perm (Vec ι)` and `S^{-1} = S.symm`; the proof is the library's. -/
theorem ddt_symm (S : Equiv.Perm (Vec ι)) (a b : Vec ι) : ddt S a b = ddt S.symm b a :=
  CipherLean.ddt_symm S a b

/-- The same lemma for a bijective function `S`, with `S^{-1} = Function.invFun S`. -/
theorem ddt_invFun (S : Vec ι → Vec ι) (hS : Function.Bijective S) (a b : Vec ι) :
    ddt S a b = ddt (Function.invFun S) b a :=
  ddt_eq_ddt_of_inverse S (Function.invFun S) (Function.leftInverse_invFun hS.1)
    (Function.rightInverse_invFun hS.2) a b

/-- On a finite type one of the two inverse equations is redundant: `T ∘ S = id` alone forces `S` to
be a permutation and `T` its two-sided inverse. -/
theorem ddt_eq_ddt_of_leftInverse (S T : Vec ι → Vec ι) (hTS : ∀ x, T (S x) = x) (a b : Vec ι) :
    ddt S a b = ddt T b a :=
  ddt_eq_ddt_of_inverse S T hTS
    ((Function.LeftInverse.rightInverse_of_surjective hTS)
      (Finite.injective_iff_surjective.mp (Function.LeftInverse.injective hTS))) a b

/-- Source: "In words: the DDT of S^{-1} is the transpose of the DDT of S." -/
theorem ddtMatrix_symm (S : Equiv.Perm (Vec ι)) :
    ddtMatrix S.symm = (ddtMatrix S).transpose := by
  ext a b
  simp only [ddtMatrix, Matrix.of_apply, Matrix.transpose_apply]
  exact (ddt_symm S b a).symm

/-! ## Finite checks — a toy instance with the expected numbers, and a counterexample for the one
hypothesis ("`T` is the inverse of `S`"); all decided on 3-bit words through `ddt_toFun` -/

section toy
open Sbox

/-- A 3-bit toy permutation: the 3-cycle `5 ↦ 6 ↦ 7 ↦ 5`, identity on `0, …, 4`. It is not an
involution and its DDT is not symmetric, so the transpose is a genuine change of table. -/
def toyTable : Vector (BitVec 3) 8 := #v[0, 1, 2, 3, 4, 6, 7, 5]

def toyS : BitVec 3 → BitVec 3 := ofTable toyTable

/-- The inverse of `toyS`, as a table (`5 ↦ 7 ↦ 6 ↦ 5`). -/
def toyInvTable : Vector (BitVec 3) 8 := #v[0, 1, 2, 3, 4, 7, 5, 6]

def toyInv : BitVec 3 → BitVec 3 := ofTable toyInvTable

theorem toyInv_toyS : ∀ x, toyInv (toyS x) = x := by decide

theorem toyS_toyInv : ∀ y, toyS (toyInv y) = y := by decide

/-- The lemma holds on the toy, entry by entry: 64 pairs `(a, b)`, 8 inputs on each side. -/
theorem toy_ddt_transpose (a b : BitVec 3) :
    ddt (toFun toyS) (toVec a) (toVec b) = ddt (toFun toyInv) (toVec b) (toVec a) := by
  rw [ddt_toFun, ddt_toFun]
  revert a b
  decide

/-- The expected numbers (Python beforehand): row `a = 1` of `DDT(toyS)` is
`[0, 4, 4, 0, 0, 0, 0, 0]`, so `ddt toyS 1 2 = 4` while `ddt toyS 2 1 = 0`; the inverse has them
exchanged. -/
theorem toy_values :
    ddt (toFun toyS) (toVec 1) (toVec 2) = 4 ∧ ddt (toFun toyS) (toVec 2) (toVec 1) = 0 ∧
      ddt (toFun toyInv) (toVec 2) (toVec 1) = 4 ∧ ddt (toFun toyInv) (toVec 1) (toVec 2) = 0 := by
  simp only [ddt_toFun]
  decide

/-- Counterexample for the hypothesis "`T` is the inverse of `S`": with `T = S` (not the inverse,
since `toyS` is not an involution) the identity fails at `(a, b) = (1, 2)`. Equivalently, the DDT of
a permutation is in general not a symmetric matrix. -/
theorem toy_not_symmetric :
    ddt (toFun toyS) (toVec 1) (toVec 2) ≠ ddt (toFun toyS) (toVec 2) (toVec 1) := by
  rw [ddt_toFun, ddt_toFun]
  decide

/-- The same for `T = id`: `ddt id 2 1 = 0` but `ddt toyS 1 2 = 4`. -/
theorem toy_id_fails :
    ddt (toFun toyS) (toVec 1) (toVec 2) ≠
      ddt (toFun (id : BitVec 3 → BitVec 3)) (toVec 2) (toVec 1) := by
  rw [ddt_toFun, ddt_toFun]
  decide

end toy

end DdtInverse

#print axioms DdtInverse.ddt_symm
#print axioms DdtInverse.ddtMatrix_symm
#print axioms DdtInverse.toy_ddt_transpose
