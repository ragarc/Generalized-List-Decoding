import Mathlib.Basic.NNReal.Star
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Prod

structure FiniteDistribution (X : Type*) [Fintype X] where
  prob : X → NNReal
  is_distribution : ∑ x, prob x = 1

namespace FiniteDistribution

variable {X Y : Type*} {f : X → Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def univ (α : Type*) [Fintype α] : Finset α := Finset.univ
def fiber (f : X → Y): Y → Finset X :=
  fun y => (univ X).filter (f · = y)
attribute [simp] univ fiber

lemma fibers_biUnion_eq_univ :
    (univ Y).biUnion (fiber f) = (univ X) := by
    ext x; simp

omit [DecidableEq X] in
lemma fibers_pairwise_disjoint :
    Set.PairwiseDisjoint (↑(univ Y))
      (fiber f) := by
    intro y1 _ y2 _ neq dX py1 py2 x hx
    simp
    have h1 := (Finset.mem_filter.mp (py1 hx)).2
    have h2 := (Finset.mem_filter.mp (py2 hx)).2
    have eq : y1 = y2 := h1.symm.trans h2
    apply neq
    exact eq

def pushforward (f : X → Y) (mu : FiniteDistribution X) : FiniteDistribution Y where
  prob y := ∑ x with f x = y, mu.prob x
  is_distribution := by
    show ∑ y ∈ (univ Y), ∑ x ∈ (fiber f y), mu.prob x = 1
    rw [← Finset.sum_biUnion fibers_pairwise_disjoint]
    rw [fibers_biUnion_eq_univ]
    exact mu.is_distribution

end FiniteDistribution
