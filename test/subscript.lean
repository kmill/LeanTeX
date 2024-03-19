import LeanTeX
import Lean.Elab.Tactic.Guard

set_option linter.unusedVariables false

open Lean

def a : Nat := 22

def real.pi : Nat := 3

open real LeanTeX in
latex_pp_const_rule pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "real.pi"

def f : Nat → Nat → Nat := λ x y => x + y

def g : Unit → Nat := λ _ => 22

open LeanTeX in
/-- An experiment: use a subscript for an argument. Represents `Fin n` as `\mathbb{N}_{<n}` -/
-- TODO make work for multi-argument like Nat → Nat → Real → Real
latex_pp_app_rules (kind := any) (paramKinds := params)
  | f, #[n] => do
    if params[0]!.bInfo.isExplicit && params[0]!.type.isConstOf `Nat then
      let f ← latexPP f
      let n ← withExtraSmallness 2 <| latexPP n
      return f.sub n
    else
      failure

variable (b : Nat) (c : Nat → Real → Real) (x : Real)

/-- info: \text{f}_{\pi + \text{a} + \text{f}_{b}(22)}(2) -/
#guard_msgs in #latex f (real.pi + a + f b 22) 2
/-- info: c_{1}(x) -/
#guard_msgs in #latex c 1 x

def foo (n : Nat) : Prop := true
/-- info: \exists x : \mathbb{N},\ \text{foo}_{x} -/
#guard_msgs in #latex Exists foo

/-- info: \operatorname{Lean}\left[\text{?foo}\right] -/
#guard_msgs in #latex ?foo
section
open scoped LeanTeX.Extra
/-- info: ?foo -/
#guard_msgs in #latex ?foo
end
