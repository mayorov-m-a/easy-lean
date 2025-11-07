import Mathlib

theorem b_eq_one_of_linear_subst (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (ha : a = 2 - b) : b = 1 := by
  have h1 : 3 * (2 - b) + 2 * b = 5 := by
    simpa [ha] using h₀
  ring_nf at h1
  linarith
