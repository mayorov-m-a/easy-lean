import Mathlib

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) :
    a = 1 ∧ b = 1 := by
  have h2' := congrArg (fun t : ℝ => (2 : ℝ) * t) h₁
  have h2 : 2 * a + 2 * b = 2 * 2 := by
    simpa [mul_add] using h2'
  have ha : a = 1 := by
    linarith [h₀, h2]
  have hsum : b + a = 2 := by simpa [add_comm] using h₁
  have hb' : b = 1 := by
    have : b + 1 = 2 := by simpa [ha, add_comm] using hsum
    linarith [this]
  exact ⟨ha, hb'⟩
