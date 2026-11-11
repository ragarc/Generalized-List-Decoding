import CsProofs.ZBJ.Definitions.Code
import CsProofs.ZBJ.Definitions.Types

structure AdversarialChannel (X S Y : Type) (n: ℕ)
[Alphabet X] [Alphabet Y] [Alphabet S]
 where
  inputConstr : Set (NType n X)
  noiseConstr : Set (NType n S)
  channel : X × S → Y

variable {n : ℕ} {X S Y : Type} [Alphabet X] [Alphabet Y] [Alphabet S]

abbrev AdvChannelCode (A : AdversarialChannel X S Y n) :=
  {C : Code n X // ∀ c ∈ C, NType.fromWord c ∈ A.inputConstr }

/-- Applies the single-letter channel to each coordinate of a codeword `x`
  and noise sequence `s`, producing the output word. -/
def AdversarialChannel.apply (A : AdversarialChannel X S Y n)
    (x : Fin n → X) (s : Fin n → S) : Fin n → Y :=
  fun i => A.channel (x i, s i)

/-- A list `L` of codewords is confusable if there is a single output word `y`
  that every codeword in `L` can be sent to by some admissible noise sequence. -/
def confusable (A : AdversarialChannel X S Y n) (L : Set (Fin n → X)) : Prop :=
  ∃ y : Fin n → Y, ∀ x ∈ L, ∃ s : Fin n → S,
    NType.fromWord s ∈ A.noiseConstr ∧ A.apply x s = y

def AdvChannelCode.isListDecodable {A : AdversarialChannel X S Y n}
  (C : AdvChannelCode A) (listSize : ℝ) : Prop :=
  ∀ L ⊆ C.val, L.card ≤ listSize → ¬ (confusable A ↑L)
