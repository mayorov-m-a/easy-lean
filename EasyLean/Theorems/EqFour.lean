import Mathlib

theorem eq_four (a b c d : Nat) : a = b → a = d → a = c → c = b := by
  intro h0 h1 h2
  simpa using Eq.trans h2.symm h0
