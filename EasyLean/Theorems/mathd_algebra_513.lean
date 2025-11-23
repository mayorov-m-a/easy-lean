import Mathlib
import EasyLean.Theorems.mathd_algebra_513_a_eq_one

theorem mathd_algebra_513
    (a b : Real) (h0 : 3 * a + 2 * b = 5) (h1 : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := mathd_algebra_513_a_eq_one a b h0 h1
  have hb : b = 1 := by
    have h1' : 1 + b = 2 := by simpa [ha] using h1
    linarith
  exact ⟨ha, hb⟩
