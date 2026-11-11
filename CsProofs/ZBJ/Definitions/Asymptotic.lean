import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import CsProofs.ZBJ.Definitions.Code


def asymptoticallyEquals (f g : ℕ → ℝ) : Prop := sorry

infix:50 " ≍ₐ " => asymptoticallyEquals

/-- For a particular code, its asymptotic rate is just
  the function-/
noncomputable def asymptoticRate {n : ℕ} {X : Type} [Alphabet X] (C : Code n X) : ℕ → ℝ :=
  fun k => (ErrorCorrectingCode.alphabetsize C) ^ ( ErrorCorrectingCode.rate C * k )
