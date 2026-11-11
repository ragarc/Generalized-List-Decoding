import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-- Bundles common assumptions on
  the alphabet of an error correcting
  code, such as finiteness, decidable
  equality, and nonemptyness -/
class Alphabet (X : Type) where
  [fintype : Fintype X]
  [decEq : DecidableEq X]
  [nonempty : Nonempty X]

attribute [instance] Alphabet.fintype Alphabet.decEq Alphabet.nonempty

instance {X Y : Type} [Alphabet X] [Alphabet Y] : Alphabet (X × Y) := {}

abbrev Code (n : ℕ) (X : Type) [Alphabet X] := Finset (Fin n → X)

class ErrorCorrectingCode (α : Type) where
  rate : α → ℝ
  alphabetsize : α → ℕ
  blocklength : α → ℕ

noncomputable instance {n : ℕ} {X : Type} [Alphabet X] :
  ErrorCorrectingCode (Code n X) where
  alphabetsize := fun _ => Fintype.card X
  blocklength  := fun _ => n
  rate         := fun C => Real.logb (Fintype.card X) C.card / n

noncomputable instance {α : Type} [ErrorCorrectingCode α] {p : α → Prop} :
  ErrorCorrectingCode (Subtype p) where
  alphabetsize := fun C => ErrorCorrectingCode.alphabetsize C.val
  blocklength  := fun C => ErrorCorrectingCode.blocklength C.val
  rate         := fun C => ErrorCorrectingCode.rate C.val
