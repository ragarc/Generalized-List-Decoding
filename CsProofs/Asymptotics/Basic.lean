import Mathlib.Analysis.Asymptotics.Defs

instance NatNorm : Norm ℕ :=
  ⟨fun n => ↑n⟩

def IsPolyTime (f : ℕ → ℝ) : Prop :=
  ∃ C k : ℕ, f =O[Filter.atTop] (fun n => C * n^k)
