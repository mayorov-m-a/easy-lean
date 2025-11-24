import Mathlib

open scoped Real

theorem mathd_algebra_513 (a b : Real) (h0 : 3 * a + 2 * b = 5) (h1 : a + b = 2) : a = 1 ∧ b = 1 := by
  have hb : b = 2 - a := by
    have ht : (a + b) - a = 2 - a := by
      simpa using congrArg (fun t => t - a) h1
    have hx : (a + b) - a = b := by
      simpa using add_sub_cancel a b
    simpa [hx] using ht
  have h2 : 3 * a + 2 * (2 - a) = 5 := by
    simpa [hb] using h0
  have h3 : 4 + a = 5 := by
    have h2' := h2
    ring_nf at h2'
    simpa using h2'
  have ha : a = 1 := by
    linarith [h3]
  have hb1 : b = 1 := by
    linarith [h1, ha]
  exact ⟨ha, hb1⟩
