import Mathlib.Data.Fintype.Basic
import CsProofs.ZBJ.Definitions.Types
import CsProofs.ZBJ.Definitions.Code


lemma lemma55 {X : Type} [Alphabet X] {n : ℕ} (C : Code n X):
  ∃ C' ⊆ C,
  (∃ τ : NType n X, ∀ c ∈ C', empiricalCounts c = τ) ∧
  ErrorCorrectingCode.rate C' ≍ ErrorCorrectingCode.rate C :=
  sorry
