import Mathlib

theorem mathd_algebra_513_a_eq_one
    (a b : Real) (h0 : 3 * a + 2 * b = 5) (h1 : a + b = 2) : a = 1 := by
  have ha : a = 1 := by
    linear_combination h0 - 2 * h1
  simpa using ha
