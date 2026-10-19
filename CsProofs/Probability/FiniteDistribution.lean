import Mathlib.Basic.NNReal.Star
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Prod

structure FiniteDistribution (α : Type*) [Fintype α] where
  prob : α → NNReal
  is_distribution : ∑ x, prob x= 1

namespace FiniteDistribution

variable {α β : Type*} {f : α → β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def univ (α : Type*) [Fintype α] : Finset α := Finset.univ
def fiber (f : α → β): β → Finset α :=
  fun y => (univ α).filter (f · = y)
attribute [simp] univ fiber

lemma fibers_biUnion_eq_univ :
    (univ β).biUnion (fiber f) = (univ α) := by
    ext x; simp

omit [DecidableEq α] in
lemma fibers_pairwise_disjoint :
    Set.PairwiseDisjoint (↑(univ β))
      (fiber f) := by
    intro y1 _ y2 _ neq dα py1 py2 x hx
    simp
    have h1 := (Finset.mem_filter.mp (py1 hx)).2
    have h2 := (Finset.mem_filter.mp (py2 hx)).2
    have eq : y1 = y2 := h1.symm.trans h2
    apply neq
    exact eq

def pushforward (f : α → β) (mu : FiniteDistribution α) :
 FiniteDistribution β where
  prob y := ∑ x with f x = y, mu.prob x
  is_distribution := by
    show ∑ y ∈ (univ β), ∑ x ∈ (fiber f y), mu.prob x = 1
    rw [← Finset.sum_biUnion fibers_pairwise_disjoint]
    rw [fibers_biUnion_eq_univ]
    exact mu.is_distribution



def event_prob (mu : FiniteDistribution α) (A : Finset α) : NNReal :=
  ∑ x ∈ A, mu.prob x


-- set_option pp.notation false in
/-- Conditioning on an event of nonzero probability. -/
noncomputable def conditional (A : Finset α) (mu : FiniteDistribution α)
    (h : event_prob mu A ≠ 0) : FiniteDistribution A where
  prob x := mu.prob x / event_prob mu A
  is_distribution := by
    have hsum : ∑ x ∈ A, mu.prob x = event_prob mu A := by
      unfold event_prob
      rfl

    have duh : HDiv.hDiv (mu.prob ↑x) (mu.event_prob A)
     = mu.prob ↑x * (mu.event_prob A)⁻¹ := by



    -- exact div_self h

omit [DecidableEq α] [Fintype β] [DecidableEq β] in

noncomputable def expectation [AddCommGroup β] [Module ℝ β]
    (mu : FiniteDistribution α) (f : α → β) : β :=
  ∑ x, mu.prob x • f x

end FiniteDistribution
