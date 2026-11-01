import Mathlib
import CipherLean

/-!
# <Slug>: <paper short title>, <Theorem label>

Source: <authors>, <venue / ePrint ID>, <Theorem X.Y>, p. <n>.
Paper statement (verbatim):
> ...

Names and encodings: `NOTATION.md` in this directory. Status and departures from the paper:
`README.md`. Checked with the toolchain pinned in the workspace `lean-toolchain`.
-/

namespace <Slug>

/-! ## Definitions — one per paper object, named as in NOTATION.md -/



/-! ## Lemmas — one per step of the paper's proof -/



/-! ## Main theorem — compile with `sorry` first, then prove -/

/-- Paper: <label>, "<verbatim conclusion>". -/
theorem main : True := by
  sorry

/-! ## Finite checks — a toy instance where the theorem holds, and one counterexample
per hypothesis the paper needs (shows the definitions encode the right objects) -/



end <Slug>

#print axioms <Slug>.main
