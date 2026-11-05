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

abbrev Code (n : ℕ) (X : Type) [Alphabet X] := Finset (Fin n → X)

class ErrorCorrectingCode (α : Type) where
  rate : α → ℝ
  alphabetsize : α → ℕ
  blocklength : α → ℕ

noncomputable instance {n : ℕ} {X : Type} [Alphabet X] :
  ErrorCorrectingCode (Code n X) where
  alphabetsize := fun _ => Fintype.card X
  blocklength := fun _ => n
  rate := fun C => Real.logb (Fintype.card X) C.card / n
