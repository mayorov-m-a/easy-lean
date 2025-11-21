import Mathlib

theorem mathd_algebra_513_b (a b : ℝ) (h1 : a + b = 2) (ha : a = 1) : b = 1 := by
  have hb' : 1 + b = 2 := by simpa [ha] using h1
  have hb'' : b = 1 := by linarith [hb']
  exact hb''
