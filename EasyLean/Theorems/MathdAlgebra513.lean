import Mathlib

theorem mathd_algebra_513
    (a b : Real) (h0 : 3 * a + 2 * b = 5) (h1 : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := by
    linear_combination h0 - (2 : ℚ) * h1
  have hb : b = 1 := by
    linarith [h1, ha]
  exact ⟨ha, hb⟩
