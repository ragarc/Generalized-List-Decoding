import CsProofs.Probability.FiniteDistribution
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open FiniteDistribution

variable {α : Type*} [Fintype α]

/-- Shannon entropy (in nats): the expected surprisal `-log (p x)`. -/
noncomputable def entropy (mu : FiniteDistribution α) : ℝ :=
  mu.expectation fun x => -Real.log (mu.prob x)
