import LeanTeX
import Lean.Elab.Tactic.Guard
--import Mathlib.Algebra.BigOperators.Basic

set_option linter.unusedVariables false

open Lean

def a : Nat := 22

abbrev Real := Nat
def Real.pi : Nat := 3

open Real LeanTeX in
latex_pp_const_rule pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "real.pi"

def f : Nat → Nat → Nat := λ x y => x + y

def g : Unit → Nat := λ _ => 22

def Finset (α : Type u) : Type u := α
def Finset.sum {α : Type u} {β : Type v} [Inhabited β] (s : Finset α) (f : α → β) : β := default

variable (b : Nat) (s : Finset Nat) (t : Nat → Finset Nat) (c : Nat → Real → Real) (x : Real)

#texify s.sum (λ x => x + 1)
#texify s.sum (λ x => 2 * x)
#texify s.sum (λ x => x + 1) * a
#texify a * s.sum (λ x => x + 1)
#texify s.sum (λ x => x + 1) + a
#texify a + s.sum (λ x => x + 1)
#texify s.sum (λ x => x + 1) * s.sum (λ x => 2 * x)
#texify λ (c : Nat) => c * s.sum (λ x => (t x).sum (λ y => x * y))
#texify s.sum id

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

#texify λ (f : Nat → Nat) => (s.sum f)^2
