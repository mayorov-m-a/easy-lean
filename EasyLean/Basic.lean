import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem eq_four_proof: ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intro a b c d hab had hac
  rw [← hac, hab]

theorem mathd_algebra_513_proof (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  constructor <;> linarith
