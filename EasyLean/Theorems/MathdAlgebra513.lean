import Mathlib

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h2 : 2 * a + 2 * b = 4 := by
    have := congrArg (fun x => (2 : ℝ) * x) h₁
    ring_nf at this
    simpa [mul_comm] using this
  have ha : a = 1 := by
    linarith [h₀, h2]
  have hb : b = 1 := by
    have h' : 1 + b = 2 := by simpa [ha, add_comm] using h₁
    linarith
  exact ⟨ha, hb⟩

