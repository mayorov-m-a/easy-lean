import Mathlib
import EasyLean.Theorems.AEqTwoSubBOfAddEqTwo
import EasyLean.Theorems.BEqOneOfLinearSubst

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  classical
  have ha : a = 2 - b := a_eq_two_sub_b_of_add_eq_two a b h₁
  have hb : b = 1 := b_eq_one_of_linear_subst a b h₀ ha
  have hsum : a + 1 = 2 := by simpa [hb] using h₁
  have ha1 : a = 1 := by linarith
  exact ⟨ha1, hb⟩
