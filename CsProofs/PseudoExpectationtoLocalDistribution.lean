import CsProofs.SumOfSquares
import CsProofs.LocalDistributions

variable {n d q : ℕ} {P : PolynomialOptimizationProblem n} (sol : PESolution n P d)

def variable_subset_marginal (S : dSubsetsOfn n d) :
    FiniteDistribution (S.supp → Fin 2):=
    {

    }

def PESolution.toLocalDistribution : LocalDistribution q n d :=
  sorry
