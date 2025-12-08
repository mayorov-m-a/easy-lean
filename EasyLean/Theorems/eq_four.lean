import Mathlib

theorem eq_four : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intro a b c d hab had hac
  exact hac.symm.trans hab
