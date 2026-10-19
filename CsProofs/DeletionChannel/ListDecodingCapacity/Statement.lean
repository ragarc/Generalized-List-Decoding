import CsProofs.Optimization
import CsProofs.DeletionChannel.ListDecodingCapacity.Basic

def BestRateforPolynomialLists  (CodeType : Type*) [ECC CodeType]
  (q : AlphabetSize) (δ : NormalizedDistance) :
  ConstrainedOptimizationProblem (ECCFamily CodeType q) :=
  {
    objective := fun C => C.rate
    constraints := { fun C => C.listSequenceIsPolynomial δ }
  }

#check BestRateforPolynomialLists

def IsListDecodingCapacity (CodeType : Type*) [ECC CodeType]
  (q : AlphabetSize) (f : NormalizedDistance → Rate) : Prop :=
  (fun δ => OptimizationProblem.val (BestRateforPolynomialLists CodeType q δ)) = (↑) ∘ f
