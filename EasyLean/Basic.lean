import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem mathd_algebra_513 (a b : ℝ)
  (h₀ : 3 * a + 2 * b = 5)
  (h₁ : a + b = 2) :
  a = 1 ∧ b = 1 := by
  constructor
  · have ha : a = 1 := by
      linarith [h₀, h₁]
    exact ha
  · have ha : a = 1 := by
      linarith [h₀, h₁]
    have hb : b = 1 := by
      linarith [h₁, ha]
    exact hb



theorem eq_four : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  sorry
