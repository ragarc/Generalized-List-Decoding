import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.Card
import CsProofs.Optimization

variable (n : ℕ)
variable {R : Type*}
variable [Ring R] [PartialOrder R] [StarRing R]

structure PseudoExpectaion (constraints : Set (MvPolynomial (Fin n) ℝ)) where
  toFun : (MvPolynomial (Fin n) ℝ) → ℝ
  PSDness : ∀ c ∈ constraints, ∀ p, toFun (c * p *p) ≥ 0

structure PolynomialOptimizationProblem where
  objective : MvPolynomial (Fin n) ℝ
  constraints : Set (MvPolynomial (Fin n) ℝ)

namespace BooleanPOP
def BooleanConstraintSet : Set (MvPolynomial (Fin n) ℝ) :=
    (fun i : Fin n => MvPolynomial.X i ^ 2 - 1) '' Set.univ
  ∪ (fun i : Fin n => 1 - MvPolynomial.X i ^ 2) '' Set.univ
end BooleanPOP

structure BinaryPolynomialOptimizationProblem extends PolynomialOptimizationProblem n where
  P_feasible_set_contained_in_hypercube : (BooleanPOP.BooleanConstraintSet n) ⊆ constraints

@[reducible]
def SubsetsOfSizeAtMost (k : ℕ) (X : Type): Set (Finset X) :=
  {x | x.card ≤ k}

noncomputable def Extend (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
  Matrix (SubsetsOfSizeAtMost d (Fin n))
  (SubsetsOfSizeAtMost d (Fin n)) (MvPolynomial (Fin n) ℝ) :=
    Matrix.of (fun I J =>
    p * (MvPolynomial.monomial ⟨I.1, fun i => if i ∈ I.1 then 1 else 0, by simp⟩ 1)
    *  (MvPolynomial.monomial ⟨J.1, fun j => if j ∈ J.1 then 1 else 0, by simp⟩ 1))

def SOSRelaxation
  (P : BinaryPolynomialOptimizationProblem n) (d : ℕ):
  ConstrainedOptimizationProblem (MvPolynomial (Fin n) ℝ → ℝ)
  :=
  { objective := (fun pE => pE P.objective)
    constraints := f '' P.constraints
  } where
    f (p : MvPolynomial (Fin n) ℝ) :=
    fun (pE : MvPolynomial (Fin n) ℝ → ℝ) =>
    Matrix.PosSemidef ((Extend n d p).map pE)
