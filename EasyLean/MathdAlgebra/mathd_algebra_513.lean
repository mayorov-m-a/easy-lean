import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) :
    a = 1 ∧ b = 1 := by
  have h₂ : 2 * a + 2 * b = 2 * 2 := by
    simpa [mul_add] using congrArg (fun x : ℝ => (2 : ℝ) * x) h₁
  have hsub : (3 * a + 2 * b) - (2 * a + 2 * b) = (5 : ℝ) - (2 * 2) := by
    simpa [h₂] using congrArg (fun t : ℝ => t - (2 * a + 2 * b)) h₀
  have ha : a = 1 := by
    ring_nf at hsub
    norm_num at hsub
    exact hsub
  have hb : b = 1 := by
    have h' : 1 + b = 2 := by simpa [ha] using h₁
    linarith
  exact ⟨ha, hb⟩
