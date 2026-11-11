import Mathlib.Probability.ProbabilityMassFunction.Constructions
import CsProofs.ZBJ.Definitions.Code

abbrev NType (n : ℕ) (X : Type) [Alphabet X]: Type :=
  {τ : X → ℕ // ∑ x, τ x = n}

namespace NType

variable {n : ℕ} {X Y : Type} [Alphabet X] [Alphabet Y]

def fromWord (word : Fin n → X) : NType n X where
  val x := (Finset.univ.filter (fun i => word i = x)).card
  property := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := word)
      (fun i _ => Finset.mem_univ (word i))]
    simp

def pushforward (τ : NType n X) (f : X → Y) : NType n Y where
  val y := ∑ x with f x = y, τ.val x
  property := by
    rw [Finset.sum_fiberwise Finset.univ f τ.val, τ.property]

/-- The X- and Y-marginals of a joint type, obtained by pushing forward
  along the two projections. -/
def marginal (τ : NType n (X × Y)) : NType n X × NType n Y :=
  (τ.pushforward Prod.fst, τ.pushforward Prod.snd)

def typeClass (τ : NType n X) : Finset (Fin n → X) :=
  Finset.univ.filter (fun word => τ.val = (fromWord word).val)


noncomputable def toPMF [NeZero n] (τ : NType n X) : PMF X :=
  PMF.ofFintype (fun x => (τ.val x : ENNReal) / n) (by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, τ.property]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (by simp))

@[simp] lemma toPMF_apply [NeZero n] (τ : NType n X) (x : X) :
    toPMF τ x = (τ.val x : ENNReal) / n := rfl


/-- The mutual information `I(X;Y)` (in base `|X|`, matching `rate`) of the joint distribution `toPMF τ`:
  `∑ p(x,y) log_|X| (p(x,y) / (p(x) p(y)))`. Terms with `p(x,y) = 0` contribute `0`.
  The empty type (`n = 0`) has no associated distribution, so it is assigned `0`. -/
noncomputable def mutualInformation (τ : NType n (X × Y)) : ℝ :=
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    let P := toPMF τ
    let Px := P.map Prod.fst
    let Py := P.map Prod.snd
    ∑ p : X × Y, (P p).toReal *
      Real.logb (Fintype.card X) ((P p).toReal / ((Px p.1).toReal * (Py p.2).toReal))

instance : Fintype (NType n X) := by
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

end NType
