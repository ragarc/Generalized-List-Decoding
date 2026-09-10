import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice


structure OptimizationProblem (X : Type) where
  feasible_set : Set X
  objective : X → EReal

structure ConstrainedOptimizationProblem (X : Type) extends OptimizationProblem X where
  constraints : Set (X → Prop)
  feasible_set := {x | ∀ c ∈ constraints, c x}

structure Solution {X : Type} (P : OptimizationProblem X) where
  point : X
  val : EReal := P.objective point
  feasible : point ∈ P.feasible_set

namespace ConstrainedOptimizationProblem



end ConstrainedOptimizationProblem

namespace OptimizationProblem

def solutionIsOptimal {X P} (x : Solution (P : OptimizationProblem X)) : Prop :=
  x.val ≥ sSup (P.objective '' P.feasible_set)

end OptimizationProblem

-- structure OptimizationNet {X} (P : OptimizationProblem X) where
--   net : Set (OptimizationProblem X)
--   same_objective : ∀ Q ∈ net, Q.objective = P.objective
--   covers_feasible : P.feasible ⊆ (⋃ Q ∈ net, Q.feasible)

-- theorem relaxation_improves_value
--   {X : Type}
--   (R P : OptimizationProblem X)
--   (hset : P.feasible_set ⊆ R.feasible_set)
--   (hobj : R.objective = P.objective) :
--   P.optimumValue ≥ R.optimumValue:= by
--   simp
--   rw [R.P_optimumValue, P₂.P_optimumValue]
--   rw [hobj]
--   exact sInf_le_sInf (image_of_subset_is_subset P₂.objective hset)
