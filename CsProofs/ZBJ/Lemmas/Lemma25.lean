import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Replicate
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CsProofs.ZBJ.Definitions.Types


/-- Establishes equivalence between NType n X and
  the set of multisets with n elements over X. -/
def NTypesEquivSym (n : ℕ) (X : Type) [Alphabet X] :
  NType n X ≃ Sym X n where
  toFun τ := ⟨∑ x, Multiset.replicate (τ.1 x) x, by
    simp [Multiset.card_sum, τ.2]⟩
  invFun s := ⟨fun x => s.1.count x, by
    calc
    _ = (s.1).card := by
      refine Multiset.sum_count_eq_card ?_
      intro a _
      refine Finset.mem_univ a
    _ = _ := s.2
  ⟩
  left_inv τ := by
    simp; apply Subtype.ext; funext x
    simp; rw [Multiset.count_sum'];
    simp only [Multiset.count_replicate]
    simp
  right_inv s := by
    simp; apply Subtype.ext;
    simp; rw [Multiset.ext];
    intros a; rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    simp


lemma Lemma25 {n : ℕ} {X : Type} [Alphabet X]:
  Fintype.card (NType n X) =
  Nat.choose (n + (Fintype.card X) - 1) (Fintype.card X - 1) :=
  by
    have hp : 1 ≤ Fintype.card X := Fintype.card_pos
    calc
      _ = Fintype.card (Sym X n) := by
        apply Fintype.card_congr
        apply NTypesEquivSym
      _ = (Fintype.card X + n - 1).choose n := by apply Sym.card_sym_eq_choose
      _ = (n + Fintype.card X - 1).choose n := by rw [Nat.add_comm]
      _ = _ := by
        apply Nat.choose_symm_of_eq_add
        apply Nat.add_sub_assoc
        exact hp
