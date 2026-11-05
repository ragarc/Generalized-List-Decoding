import Mathlib.Probability.ProbabilityMassFunction.Basic
import CsProofs.ZBJ.Definitions.Code

abbrev NType (n : ℕ) (X : Type) [Alphabet X]: Type :=
  {τ : X → ℕ // ∑ x, τ x = n}

def empiricalCounts {n : ℕ} {X : Type} [Alphabet X] (word : Fin n → X) : NType n X :=
  ⟨fun x => (Finset.univ.filter (fun i => word i = x)).card, by
    rw [← Finset.card_eq_sum_card_fiberwise (f := word)
      (fun i _ => Finset.mem_univ (word i))]
    simp⟩

def typeClass {n : ℕ} {X : Type} [Alphabet X]
  (τ : NType n X) : Finset (Fin n → X) :=
  Finset.univ.filter (fun word => τ.val = (empiricalCounts word).val)

instance {n : ℕ} {X : Type} [Alphabet X] :
  Fintype (NType n X) := by
  exact Fintype.subtype
    ((Fintype.piFinset (fun _ : X => Finset.range (n + 1))).filter
      (fun τ => ∑ x, τ x = n))
    (by
      intro τ
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        refine ⟨fun x => ?_, h⟩
        have : τ x ≤ ∑ y, τ y :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
        omega)
