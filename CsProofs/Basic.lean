import Mathlib.Data.Set.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

opaque NodeDimension : Type
opaque NuclearNormBound : Type
opaque NormalizedSplitOperator : Type
opaque LiftedRightDegreeMatrix : Type
opaque LiftedSplitMatrix : Type

structure SplitNode where
  k : ℕ
  left : Finset (Fin k)
  right : Finset (Fin k)
  disjoint : Disjoint left right
  union_eq : left ∪ right = Finset.univ

structure SplitGraph (X : Type) where
  L : Finset X
  R : Finset X
  edges : Finset (L × R)
  edge_weights : edges -> ℝ

def findNodeDimension (v : SplitNode) : NodeDimension :=
  sorry

def findNodeBound (v : SplitNode) : NuclearNormBound :=
  sorry

def findLiftedRightDegreeMatrix (v : SplitNode) : LiftedRightDegreeMatrix :=
  sorry

-- def findSplitGraph (v : SplitNode) : SplitGraph :=
-- sorry

def graphToLiftedSplitMatrix {X} (G : SplitGraph X) (labels : Finset ℕ): Matrix (G.L × labels) (G.R × labels) ℝ:=
sorry



-- it seems like there is still work to be done. Work in the
-- sense of having good *design* choices, which is fun.


-- it also seems like we have a general principle. To maximize
-- an object, it also suffices to maximize over a partition of
-- the space. It would be really exciting if I was able to prove
-- this principle, and use it in the formalization of this algorithm.
