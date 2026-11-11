import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Data.EReal.Basic

structure ConstrainedOptimizationProblem (D : Type) where
  constraint :  Set D
  objective   : D → ℝ

namespace ConstrainedOptimizationProblem

variable {D : Type}

noncomputable def maximumOver
    (constraint : Set D) (objective : D → EReal) : EReal :=
  ⨆ x ∈ constraint, objective x

noncomputable def minimumOver
    (constraint : Set D) (objective : D → EReal) : EReal :=
  ⨅ x ∈ constraint, objective x

end ConstrainedOptimizationProblem

/-- `maximum x ∈ S, f x` is notation for `maximumOver S (fun x ↦ f x)`. -/
syntax (name := maximumNotation) "maximum " ident " ∈ " term ", " term:67 : term

macro_rules (kind := maximumNotation)
  | `(maximum $x:ident ∈ $S, $v) =>
    `(ConstrainedOptimizationProblem.maximumOver $S (fun $x ↦ $v))

@[app_unexpander ConstrainedOptimizationProblem.maximumOver]
def maximumOver.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $S fun $x:ident ↦ $v) => `(maximum $x:ident ∈ $S, $v)
  | _ => throw ()



/-- `minimum x ∈ S, f x` is notation for `minimumOver S (fun x ↦ f x)`. -/
syntax (name := minimumNotation) "minimum " ident " ∈ " term ", " term:67 : term

macro_rules (kind := minimumNotation)
  | `(minimum $x:ident ∈ $S, $v) =>
    `(ConstrainedOptimizationProblem.minimumOver $S (fun $x ↦ $v))

@[app_unexpander ConstrainedOptimizationProblem.minimumOver]
def minimumOver.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $S fun $x:ident ↦ $v) => `(minimum $x:ident ∈ $S, $v)
  | _ => throw ()
