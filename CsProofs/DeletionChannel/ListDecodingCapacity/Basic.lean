import Init.Prelude
import Mathlib.Analysis.SpecialFunctions.Log.Base
import CsProofs.Asymptotics.Basic
import CsProofs.Optimization
import CsProofs.DeletionChannel.ListDecodingCapacity.ErrorCorrectingCode

def ECCFamily (CodeType : Type*) [ECC CodeType] (q : AlphabetSize) :=
  {C : ℕ → CodeType // StrictMono (fun i => ECC.blockLength (C i)) ∧ ∀ i, ECC.alphabetSize (C i) = q}

instance {CodeType : Type*} [ECC CodeType] {q : AlphabetSize} :
  CoeFun (ECCFamily CodeType q) (fun _ => ℕ → CodeType) := ⟨Subtype.val⟩

namespace ECCFamily

  variable  {CodeType : Type*} {q : AlphabetSize} [ECC CodeType] (C : ECCFamily CodeType q)

  def listSequenceIsPolynomial (δ : NormalizedDistance) : Prop :=
    ∃ (c k : ℕ), ∀ (i : ℕ), let P := C i
      ECC.maxListSize P δ ≤ c * (ECC.blockLength P)^k

  def rate : Rate :=
    ECC.rate (C 1) /- FIX LATER, SHOULD BE THE LIMINF -/

end ECCFamily
