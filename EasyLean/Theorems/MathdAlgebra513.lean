import Mathlib

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h₂ := by
    simpa [mul_add] using congrArg (fun t : ℝ => (2 : ℝ) * t) h₁
  have ha : a = 1 := by
    linarith [h₀, h₂]
  have hb : b = 1 := by
    linarith [h₁, ha]
  exact ⟨ha, hb⟩
