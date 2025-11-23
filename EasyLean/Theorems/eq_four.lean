import Mathlib

theorem eq_four
    (a b c d : Nat) (h₁ : a = b) (h₂ : a = d) (h₃ : a = c) : c = b := by
  exact (Eq.trans (Eq.symm h₃) h₁)
