import Formal.Crypto.F2.Vec

/-!
# `Formal.Crypto.Sbox` — S-boxes from lookup tables, and their transport to `F_2^n`

A concrete S-box is a table on `BitVec n` (`ofTable`), so that `decide` can evaluate it;
`toFun S` is the same map on `Vec (Fin n)` through the bridge `bvEquiv`, which is where the
library's statistics (`ddt`, `walsh`) are stated. The PRESENT S-box is included as the standard
test instance (A. Bogdanov et al., *PRESENT: An Ultra-Lightweight Block Cipher*, CHES 2007).
-/

namespace Crypto
namespace Sbox

variable {n : ℕ}

/-- An `n`-bit S-box given by its lookup table: entry `i` is the image of the word of value `i`. -/
def ofTable (t : Vector (BitVec n) (2 ^ n)) (x : BitVec n) : BitVec n := t[x.toNat]'x.isLt

/-- The S-box as a map on `F_2^n`, through the bridge `bvEquiv`. -/
def toFun (S : BitVec n → BitVec n) : Vec (Fin n) → Vec (Fin n) := fun v => toVec (S (ofVec v))

theorem toFun_apply (S : BitVec n → BitVec n) (v : Vec (Fin n)) : toFun S v = toVec (S (ofVec v)) :=
  rfl

theorem toFun_eq_comp (S : BitVec n → BitVec n) : toFun S = bvEquiv ∘ S ∘ bvEquiv.symm := rfl

theorem toFun_toVec (S : BitVec n → BitVec n) (x : BitVec n) : toFun S (toVec x) = toVec (S x) := by
  rw [toFun_apply, ofVec_toVec]

theorem toFun_bijective {S : BitVec n → BitVec n} (hS : Function.Bijective S) :
    Function.Bijective (toFun S) := by
  rw [toFun_eq_comp]
  exact bvEquiv.bijective.comp (hS.comp bvEquiv.symm.bijective)

/-- On a finite type, injectivity (checked by `decide` for a table) already gives bijectivity. -/
theorem bijective_of_injective {S : BitVec n → BitVec n} (h : Function.Injective S) :
    Function.Bijective S :=
  Finite.injective_iff_bijective.mp h

/-- A bijective S-box as a permutation of `F_2^n` (noncomputable inverse). -/
noncomputable def toPerm (S : BitVec n → BitVec n) (hS : Function.Bijective S) :
    Equiv.Perm (Vec (Fin n)) :=
  Equiv.ofBijective (toFun S) (toFun_bijective hS)

@[simp] theorem toPerm_apply (S : BitVec n → BitVec n) (hS : Function.Bijective S)
    (v : Vec (Fin n)) : toPerm S hS v = toFun S v := rfl

/-! ## The PRESENT S-box, the library's standard 4-bit test instance -/

/-- The PRESENT S-box table (Bogdanov et al., CHES 2007, Section 3). -/
def presentTable : Vector (BitVec 4) 16 :=
  #v[0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]

/-- The PRESENT S-box on 4-bit words. -/
def present : BitVec 4 → BitVec 4 := ofTable presentTable

theorem present_bijective : Function.Bijective present :=
  bijective_of_injective (by decide)

/-- The PRESENT S-box on `F_2^4`. -/
def presentVec : Vec (Fin 4) → Vec (Fin 4) := toFun present

theorem presentVec_bijective : Function.Bijective presentVec := toFun_bijective present_bijective

end Sbox
end Crypto
