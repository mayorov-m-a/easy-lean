import Mathlib

open scoped Classical

noncomputable def universal_rational_sequence (n : ℕ) : ℚ :=
  (Encodable.decode₂ (ℚ × ℚ) n).elim 0 fun p => p.1 + p.2 * (n : ℚ)
