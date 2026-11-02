/-
Copyright (c) 2026 Kai Hu. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Kai Hu
-/
import CipherLean.Lib.F2.Vec
import CipherLean.Lib.F2.Subspace
import CipherLean.Lib.F2.Affine
import CipherLean.Lib.Sbox
import CipherLean.Lib.Walsh
import CipherLean.Lib.DDT
import CipherLean.Lib.Links
import CipherLean.Lib.Chi

/-!
# `CipherLean` — umbrella module of the shared cryptanalysis library

`import CipherLean` brings in the carrier `Vec ι`, characters and subspaces of `F_2^ι`, masks
constant on a set with `λ^⊥` and `dir Aff` (`F2.Affine`), Walsh coefficients, the DDT with the
derivative, the two difference sets and `K_H(α)` of a map, the Chabaud–Vaudenay link, table
S-boxes, and the χ map of Keccak. See `README.md` and
`NOTATION.md` in `CipherLean/Lib/`.
-/
