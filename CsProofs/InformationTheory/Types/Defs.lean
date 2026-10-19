import CsProofs.FiniteDistribution
import Mathlib.Data.Fintype.Basic

/-- Types (empirical distributions) of length n over X, stored as symbol counts. -/
def NType (n : ℕ) (X : Type) [Fintype X] :=
  { c : X → ℕ // ∑ x, c x = n }
