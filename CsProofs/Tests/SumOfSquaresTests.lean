
-- Test 1: Verify {3, 4, 1} is in SubsetsOfSizeAtMost 4 (Fin 5)
example : ({3, 4, 1} : Finset (Fin 5)) ∈ SubsetsOfSizeAtMost 4 (Fin 5) := by
  decide
-- Finset can be evaluated directly!
#eval ({3, 4, 1} : Finset (Fin 5))
-- InfoView outputs: {1, 3, 4}
