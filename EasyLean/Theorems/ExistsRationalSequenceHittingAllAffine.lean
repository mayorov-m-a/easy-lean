import Mathlib
import EasyLean.Definitions.UniversalRationalSequence

open scoped Classical

theorem exists_rational_sequence_hitting_all_affine :
    ∃ s : ℕ → ℚ, ∀ a d : ℚ, ∃ t : ℕ, s t = a + d * (t : ℚ) := by
  classical
  refine ⟨universal_rational_sequence, ?_⟩
  intro a d
  refine ⟨Encodable.encode (a, d), ?_⟩
  let t : ℕ := Encodable.encode (a, d)
  have ht : Encodable.decode₂ (ℚ × ℚ) t = some (a, d) := by
    simpa [t] using (Encodable.encodek₂ (α := ℚ × ℚ) (a := (a, d)))
  -- Now unfold the definition at n = t and use ht
  change universal_rational_sequence t = a + d * t
  dsimp [universal_rational_sequence]
  simpa [ht]
