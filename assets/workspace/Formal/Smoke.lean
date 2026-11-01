import Mathlib

/-- Smoke test: Mathlib loads and the kernel accepts a trivial theorem. -/
theorem smoke_test : (2 : ℤ) + 2 = 4 := by norm_num

#print axioms smoke_test
