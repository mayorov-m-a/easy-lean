import Mathlib
import EasyLean.Mathd.Algebra.mathd_algebra_513_a
import EasyLean.Mathd.Algebra.mathd_algebra_513_b

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := mathd_algebra_513_a a b h₀ h₁
  have hb : b = 1 := mathd_algebra_513_b a b h₁ ha
  exact ⟨ha, hb⟩
