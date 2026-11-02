/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.DDT
import Mathlib.Data.Fin.VecNotation

/-!
# `CipherLean.Lib.Chi` — the χ map on a cycle of length `r`

`chiMap r z i = z i + (z (i + 1) + 1) * z (i + 2)`, indices modulo `r` (`Fin r` arithmetic): the
nonlinear layer of Keccak (J. Daemen, *Cipher and Hash Function Design*, PhD thesis, KU Leuven 1995),
as written in Andreoli, Leander, Piccione, Stennes, "Generalizations of ChiChi", ToSC 2025(3), §2,
and in the ChiChi paper formalized in `WHConj3`, §2.2. It is a permutation of `F_2^r` exactly when
`r` is odd (Daemen 1995; ALPS25 Lemma 1 citing Liu–Sarkar–Meier–Isobe, J. Cryptology 2022); the finite
checks show `r = 3` bijective and `r = 4` not. The name is `chiMap` because `chi` is the character
`(-1)^{w·x}` of `CipherLean.Lib.F2.Vec`.

`deriv_chiMap_apply` is the coordinate form of the difference `Δ_d χ_r(x)` (ChiChi paper, §3.4,
eq. ordinary-chi-difference).
-/

namespace CipherLean

/-- The χ map on a cycle of length `r`: `(χ_r z)_i = z_i + (z_{i+1} + 1) z_{i+2}`, indices mod `r`. -/
def chiMap (r : ℕ) [NeZero r] (z : Vec (Fin r)) : Vec (Fin r) :=
  fun i => z i + (z (i + 1) + 1) * z (i + 2)

/-- The coordinates of `Δ_d χ_r(x)`:
`d_i + d_{i+2} + d_{i+1} d_{i+2} + d_{i+1} x_{i+2} + d_{i+2} x_{i+1}`. -/
theorem deriv_chiMap_apply (r : ℕ) [NeZero r] (d x : Vec (Fin r)) (i : Fin r) :
    deriv (chiMap r) d x i =
      d i + d (i + 2) + d (i + 1) * d (i + 2) + d (i + 1) * x (i + 2) + d (i + 2) * x (i + 1) := by
  simp only [deriv, chiMap, Pi.add_apply]
  generalize x i = x0
  generalize x (i + 1) = x1
  generalize x (i + 2) = x2
  generalize d i = d0
  generalize d (i + 1) = d1
  generalize d (i + 2) = d2
  revert x0 x1 x2 d0 d1 d2
  decide

/-- Finite check: `χ_3(1, 0, 0) = (1, 1, 0)`. -/
theorem chiMap_three_example : chiMap 3 ![1, 0, 0] = ![1, 1, 0] := by decide

/-- `χ_3` is a permutation (odd length). -/
theorem chiMap_three_bijective : Function.Bijective (chiMap 3) := by decide

/-- `χ_4` is not a permutation (even length). -/
theorem chiMap_four_not_bijective : ¬ Function.Bijective (chiMap 4) := by decide

end CipherLean
