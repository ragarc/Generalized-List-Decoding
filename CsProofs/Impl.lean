import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Union

structure FinitePartition (k : ℕ) where
  blocks : Finset (Finset (Fin k))

  nonempty_blocks : ∀ b ∈ blocks, b.Nonempty
  pairwise_disjoint : (blocks : Set (Finset (Fin k))).PairwiseDisjoint id
  covers : blocks.biUnion id = (Finset.univ: Finset (Fin k))


def PartitionSequence (n k : ℕ) : Type := Fin n → FinitePartition k
