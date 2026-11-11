import Mathlib.Data.Fintype.Basic
import CsProofs.ZBJ.Definitions.Code
import CsProofs.ZBJ.Definitions.Asymptotic
import CsProofs.ZBJ.Definitions.Types

lemma lemma55 {X : Type} [Alphabet X] {n : ℕ} (C : Code n X):
  ∃ C' ⊆ C,
  (∃ τ : NType n X, ∀ c ∈ C', NType.fromWord c = τ) ∧
  asymptoticRate C' ≍ₐ asymptoticRate C :=
  sorry
