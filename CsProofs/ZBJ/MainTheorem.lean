import CsProofs.ZBJ.Definitions.AdversarialChannel
import CsProofs.ZBJ.Definitions.Optimization

variable {X S Y : Type} {n : ℕ} [Alphabet X] [Alphabet Y] [Alphabet S]

open ConstrainedOptimizationProblem

/-- The paper writes this as λₛ|ₓ -/
def condNType (Px : NType n X) (Λs : Set (NType n S)) : Set (NType n (X × S)) :=
  {σ | σ.marginal.1 = Px ∧ σ.marginal.2 ∈ Λs}

noncomputable def capacityOf (A : AdversarialChannel X S Y n) : EReal :=
  match A with
  | ⟨Λx, Λs, W⟩ =>
      maximum Px ∈ Λx, minimum Pxs ∈ condNType Px Λs,
        let Pxy : NType n (X × Y) := Pxs.pushforward (fun (x, s) => (x, W (x, s)))
        (NType.mutualInformation Pxy : EReal)

def ListDecodingCapacityStatement : Prop :=
  ∀ {X S Y : Type} {n : ℕ} [Alphabet X] [Alphabet Y] [Alphabet S]
    (A : AdversarialChannel X S Y n),
  ∀ C : AdvChannelCode A, ∀ δ ∈ Set.Icc (0:ℝ) 1,
    ErrorCorrectingCode.rate C ≥ (capacityOf A) + δ
    → C.isListDecodable (ErrorCorrectingCode.rate C ^ (n*δ))
