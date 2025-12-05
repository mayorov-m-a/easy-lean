import Mathlib

theorem mathd_algebra_513
    (a b : Real)
    (h0 : 3 * a + 2 * b = 5)
    (h1 : a + b = 2) :
    a = 1 ∧ b = 1 := by
  -- Subtract 2*(a+b) from h0 and then use h1 to simplify the right-hand side
  have hsub : (3 * a + 2 * b) - 2 * (a + b) = (5 : Real) - 2 * 2 := by
    have h := congrArg (fun x : Real => x - 2 * (a + b)) h0
    simpa [h1] using h
  -- Expand and normalize to get a = 1
  have ha : a = 1 := by
    have hsub' : (3 * a + 2 * b) - (2 * a + 2 * b) = (5 : Real) - 2 * 2 := by
      simpa [mul_add] using hsub
    have hnorm := hsub'
    ring_nf at hnorm
    exact hnorm
  -- Get b from a + b = 2
  have hb : b = 1 := by
    have h1' : 1 + b = 2 := by simpa [ha] using h1
    linarith [h1']
  exact ⟨ha, hb⟩
