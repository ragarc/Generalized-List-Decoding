import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import CsProofs.FiniteDistribution


structure dSubsetsOfn (n d : ℕ) where
  supp : Finset (Fin n)
  card_le : supp.card ≤ d

def restrict {n} {S T : Finset (Fin n)} (h : S ⊆ T) (q : ℕ) :
    (T → Fin q) → (S → Fin q) :=
  fun a x => a ⟨x.1, h x.2⟩

lemma restrict_refl {n q} (S : Finset (Fin n)) :
    restrict (le_refl S) q = id := by
  funext a x; rfl

lemma restrict_trans {n q} {S T U : Finset (Fin n)} (h1 : S ⊆ T) (h2 : T ⊆ U) :
    restrict h1 q ∘ restrict h2 q = restrict (h1.trans h2) q := by
  funext a x; rfl

structure LocalDistribution (q n d : ℕ) where
  mu : (S : dSubsetsOfn n d) → FiniteDistribution (S.supp → Fin q)
  consistent : ∀ (S T : dSubsetsOfn n d) (h : S.supp ⊆ T.supp),
    (mu T).pushforward (restrict h q) = mu S
