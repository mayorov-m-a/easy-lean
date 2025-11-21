import Mathlib

theorem mathd_algebra_513
    (a b : ℝ)
    (h₀ : 3 * a + 2 * b = 5)
    (h₁ : a + b = 2) :
    a = 1 ∧ b = 1 := by
  have hba : b + a = 2 := by simpa [add_comm] using h₁
  have hb : b = 2 - a := (eq_sub_iff_add_eq).2 hba
  have h2 : 3 * a + 2 * (2 - a) = 5 := by simpa [hb] using h₀
  have ha : a = 1 := by
    have h2' := h2
    ring_nf at h2'
    linarith [h2']
  have hb1 : b = 1 := by linarith [h₁, ha]
  exact ⟨ha, hb1⟩
