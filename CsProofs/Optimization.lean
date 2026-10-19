import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Defs

class OptimizationProblem (T : Type*) where
  Point       : Type*
  feasibleSet : T → Set Point
  objective   : T → Point → EReal

export OptimizationProblem (feasibleSet objective)

structure Solution {T : Type*} [OptimizationProblem T] (prob : T) where
  point    : OptimizationProblem.Point T
  feasible : point ∈ feasibleSet prob

namespace OptimizationProblem

noncomputable def val {T : Type*} [OptimizationProblem T] (prob : T) : EReal :=
  sSup (objective prob '' feasibleSet prob)

def solutionIsOptimal {T : Type*} [OptimizationProblem T] {prob : T}
    (s : Solution prob) : Prop :=
  objective prob s.point ≥ sSup (objective prob '' feasibleSet prob)

end OptimizationProblem



structure ConstrainedOptimizationProblem (X : Type*) where
  objective : X → EReal
  constraints : Set (X → Prop)

instance {X : Type*} : OptimizationProblem (ConstrainedOptimizationProblem X) where
  Point := X
  feasibleSet P := {x | ∀ c ∈ P.constraints, c x}
  objective P := P.objective
