import Mathlib
import EasyLean.Theorems.a_eq_lincomb

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have hlin := a_eq_lincomb a b
  have hcalc : a = (5 : ℝ) - 2 * 2 := by simpa [h₀, h₁] using hlin
  have ha : a = 1 := by
    have : (5 : ℝ) - 2 * 2 = 1 := by norm_num
    simpa [this] using hcalc
  have hb : b = 1 := by
    have hb1 : 1 + b = (2 : ℝ) := by simpa [ha] using h₁
    linarith
  exact ⟨ha, hb⟩
