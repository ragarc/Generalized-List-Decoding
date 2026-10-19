import Init.Prelude

import Mathlib.Basic.Real.Basic

abbrev Rate := ℝ
abbrev BlockLength := ℕ
abbrev NormalizedDistance := ℝ
abbrev AlphabetSize := ℕ
abbrev ListSize := ℕ

class ECC (CodeType : Type*) where
  blockLength  : CodeType → BlockLength
  alphabetSize : CodeType → AlphabetSize
  rate         : CodeType → Rate
  maxListSize  : CodeType → NormalizedDistance → ListSize
