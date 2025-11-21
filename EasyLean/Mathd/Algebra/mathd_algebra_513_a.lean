import Mathlib

theorem mathd_algebra_513_a (a b : ℝ) (h0 : 3 * a + 2 * b = 5) (h1 : a + b = 2) : a = 1 := by
  have : a = 1 := by
    linear_combination h0 - (2 : ℝ) * h1
  exact this
