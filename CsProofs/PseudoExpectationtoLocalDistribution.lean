import CsProofs.SumOfSquares
import CsProofs.LocalDistributions

variable {n d q : ℕ} {P : PolynomialOptimizationProblem n}

def LocalDistribution.ofPESolution
    (sol : Solution (SOSRelaxation n P d)) : LocalDistribution q n d :=
  sorry
