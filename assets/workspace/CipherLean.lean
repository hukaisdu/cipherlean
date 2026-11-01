import CipherLean.Lib.F2.Vec
import CipherLean.Lib.F2.Subspace
import CipherLean.Lib.Sbox
import CipherLean.Lib.Walsh
import CipherLean.Lib.DDT
import CipherLean.Lib.Links

/-!
# `CipherLean` — umbrella module of the shared cryptanalysis library

`import CipherLean` brings in the carrier `Vec ι`, characters and subspaces of `F_2^ι`,
Walsh coefficients, the DDT, the Chabaud–Vaudenay link, and table S-boxes. See `README.md` and
`NOTATION.md` in `CipherLean/Lib/`.
-/
