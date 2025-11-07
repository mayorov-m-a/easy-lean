import Mathlib

-- Port of mathd_algebra_513 with proof supplied by theorem prover.
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) :
    a = 1 ∧ b = 1 := by
  have ha' : a = 2 - b := by
    linarith [h₁]
  have hb : b = 1 := by
    have h₂ : 3 * (2 - b) + 2 * b = 5 := by
      simpa [ha'] using h₀
    ring_nf at h₂
    linarith [h₂]
  have ha : a = 1 := by
    have h₁' : a + 1 = 2 := by simpa [hb] using h₁
    linarith [h₁']
  exact ⟨ha, hb⟩
