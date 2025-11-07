import Mathlib

theorem a_eq_two_sub_b_of_add_eq_two (a b : ℝ) (h : a + b = 2) : a = 2 - b := by
  have := congrArg (fun t => t - b) h
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
