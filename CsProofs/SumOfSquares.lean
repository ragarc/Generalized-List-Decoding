import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.Card
import CsProofs.Optimization
import CsProofs.LocalDistributions

variable (n : ℕ)
variable {R : Type*}
variable [Ring R] [PartialOrder R] [StarRing R]

structure PseudoExpectation (constraints : Set (MvPolynomial (Fin n) ℝ)) where
  toFun : (MvPolynomial (Fin n) ℝ) → ℝ
  PSDness : ∀ c ∈ constraints, ∀ p, toFun (c * p *p) ≥ 0

structure PolynomialOptimizationProblem where
  objective : MvPolynomial (Fin n) ℝ
  constraints : Set (MvPolynomial (Fin n) ℝ)

namespace BooleanPOP
def BooleanConstraintSet (n : ℕ): Set (MvPolynomial (Fin n) ℝ) :=
    (fun i : Fin n => MvPolynomial.X i ^ 2 - 1) '' Set.univ
  ∪ (fun i : Fin n => 1 - MvPolynomial.X i ^ 2) '' Set.univ
end BooleanPOP

structure BinaryPolynomialOptimizationProblem extends PolynomialOptimizationProblem n where
  P_feasible_set_contained_in_hypercube : (BooleanPOP.BooleanConstraintSet n) ⊆ constraints

noncomputable def Extend (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
  Matrix (dSubsetsOfn n d)
  (dSubsetsOfn n d) (MvPolynomial (Fin n) ℝ) :=
    Matrix.of (fun I J =>
    p * (MvPolynomial.monomial ⟨I.1, fun i => if i ∈ I.1 then 1 else 0, by simp⟩ 1)
    *  (MvPolynomial.monomial ⟨J.1, fun j => if j ∈ J.1 then 1 else 0, by simp⟩ 1))

def poly_constraint_to_SOS_constraint {n:ℕ} (d : ℕ) (constraint : MvPolynomial (Fin n) ℝ) :
  (MvPolynomial (Fin n) ℝ → ℝ) → Prop  :=
  fun pE => Matrix.PosSemidef ((Extend n d constraint).map pE)


/--
  For a discrete polynomial optimization problem P = ( f : R^n -> R, {c_i : R^n -> {0,1}} )
  where f and c_i are polynomials, and whose feasible set is contained in the hypercube,
  we can write down a SOS Relaxation for it.

  We are optimizing over linear functionals R[X_1, ..., X_n] -> R that satisfy certain PSD
  constraints derived from c_i.
-/
def SOSRelaxation
  (P : PolynomialOptimizationProblem n) (d : ℕ):
  ConstrainedOptimizationProblem (MvPolynomial (Fin n) ℝ → ℝ)
  :=
  { objective := (fun pE => pE P.objective)
    constraints := (poly_constraint_to_SOS_constraint d) '' P.constraints
  }

structure PESolution (P : PolynomialOptimizationProblem n) (d : ℕ) where
  sol : Solution (SOSRelaxation n P d).toOptimizationProblem
