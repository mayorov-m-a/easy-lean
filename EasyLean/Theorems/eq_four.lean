import Mathlib

theorem eq_four : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intro a b c d h1 h2 h3
  simpa using (Eq.trans h3.symm h1)
