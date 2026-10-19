-- structure DeletionChannelCode where
--   n : BlockLength
--   q : AlphabetSize
--   codewords : Finset (Fin n → Fin q)

-- namespace DeletionChannelCode

-- variable {n : BlockLength} {q : AlphabetSize} (C : DeletionChannelCode)

-- def maxListSize (C : DeletionChannelCode) (δ : NormalizedDistance) : ℕ := sorry

-- noncomputable def R : Rate :=
--   Real.logb C.q (C.codewords.card / C.n)

-- noncomputable def toParameters : ECCParameters :=
--   { q := C.q, R := C.R, n := C.n, max_list_size := C.maxListSize }

-- end DeletionChannelCode
