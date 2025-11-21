import Mathlib

theorem eq_four
    (a b c d : Nat)
    (h₀ : a = b)
    (h₁ : a = d)
    (h₂ : a = c) :
    c = b := by
  exact h₂.symm.trans h₀
