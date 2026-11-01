import CipherLean

/-!
# Example 2: analysing an S-box table with the shared library

The S-box is a table on words (`CipherLean.Sbox.ofTable`); `CipherLean.Sbox.toFun` moves it to
`F_2^n`, where the library states the DDT facts. The general theorem (every DDT row sums to `2^n`)
is the library's `CipherLean.ddt_row_sum`; the finite facts about a concrete table are decided on
words through the bridge `CipherLean.ddt_toFun` / `CipherLean.diffUniformity_toFun_le_iff`, which
is fast, instead of on `Vec (Fin n)`, which is slow in the kernel.

Concrete instance: the cube map `x ↦ x³` of `GF(2³)`, the field represented modulo `x³ + x + 1`,
written as a table. It is a permutation and APN (differential uniformity `2`); K. Nyberg,
*Differentially Uniform Mappings for Cryptography*, EUROCRYPT 1993, proves this for `x^{2^k+1}` with
`gcd(k, n) = 1`. Both facts are decided from the table here, not quoted.
-/

namespace SboxDDT

open CipherLean CipherLean.Sbox

/-- Every row of the DDT of an `n`-bit S-box sums to `2^n`: the library theorem specialised to a
table S-box on words. -/
theorem ddt_row_sum {n : ℕ} (S : BitVec n → BitVec n) (a : Vec (Fin n)) :
    ∑ b, ddt (toFun S) a b = 2 ^ n :=
  ddt_toFun_row_sum S a

/-- The cube map of `GF(2³)` as a table (`x ↦ x³`, polynomial `x³ + x + 1`): computed beforehand. -/
def cubeTable : Vector (BitVec 3) 8 := #v[0, 1, 3, 4, 5, 6, 7, 2]

/-- The cube S-box on 3-bit words. -/
def cube : BitVec 3 → BitVec 3 := ofTable cubeTable

theorem cube_bijective : Function.Bijective cube := bijective_of_injective (by decide)

/-- The cube map is APN: every off-row DDT entry is at most `2` (decided on words through the
bridge) and the entry at `(a, b) = (1, 1)` equals `2`. -/
theorem cube_isAPN : IsAPN (toFun cube) := by
  unfold IsAPN
  apply le_antisymm
  · exact (diffUniformity_toFun_le_iff cube).mpr (by decide +kernel)
  · have h := ddt_le_diffUniformity (toFun cube) (a := toVec (1 : BitVec 3))
      (fun h0 => by have := congrFun h0 0; simp [toVec_apply] at this) (toVec (1 : BitVec 3))
    rw [ddt_toFun] at h
    have h2 : (Finset.univ.filter fun x : BitVec 3 =>
        cube (x ^^^ 1) ^^^ cube x = 1).card = 2 := by
      decide +kernel
    omega

/-- The PRESENT S-box shipped with the library has differential uniformity `4`
(`CipherLean.present_diffUniformity`), so it is not APN. -/
theorem present_not_apn : ¬ IsAPN presentVec := by
  unfold IsAPN
  rw [present_diffUniformity]
  decide

end SboxDDT

#print axioms SboxDDT.ddt_row_sum
#print axioms SboxDDT.cube_isAPN
