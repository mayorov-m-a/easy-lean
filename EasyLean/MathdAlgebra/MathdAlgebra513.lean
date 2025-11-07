import Mathlib
import EasyLean.MathdAlgebra.TwoSubOneReal

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) :
    a = 1 ∧ b = 1 := by
  have hb : b = 2 - a := by
    have : b + a = 2 := by simpa [add_comm] using h₁
    exact (eq_sub_iff_add_eq).2 this
  have h2 : 3 * a + 2 * (2 - a) = 5 := by
    simpa [hb] using h₀
  have h3 : a + 4 = 5 := by
    have hlin : 3 * a + 2 * (2 - a) = a + 4 := by ring
    simpa [hlin] using h2
  have ha : a = 1 := by
    linarith [h3]
  have hb' : b = 1 := by
    simpa [ha, two_sub_one_real] using hb
  exact ⟨ha, hb'⟩
