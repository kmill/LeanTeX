import LeanTeX.Builtins
import Std.Tactic.GuardMsgs
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

/-- info: \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex s.sum (λ x => x + 1)
/-- info: \sum_{x \in s}2 \cdot x -/
#guard_msgs in #latex s.sum (λ x => 2 * x)
/-- info: \left(\sum_{x \in s}(x + 1)\right) \cdot \text{a} -/
#guard_msgs in #latex s.sum (λ x => x + 1) * a
/-- info: \text{a} \cdot \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex a * s.sum (λ x => x + 1)
/-- info: \left(\sum_{x \in s}(x + 1)\right) + \text{a} -/
#guard_msgs in #latex s.sum (λ x => x + 1) + a
/-- info: \text{a} + \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex a + s.sum (λ x => x + 1)
/-- info: \left(\sum_{x \in s}(x + 1)\right) \cdot \sum_{x \in s}2 \cdot x -/
#guard_msgs in #latex s.sum (λ x => x + 1) * s.sum (λ x => 2 * x)
/-- info: (c : \mathbb{N}) \mapsto c \cdot \sum_{x \in s}\sum_{y \in t_{x}}x \cdot y -/
#guard_msgs in #latex λ (c : Nat) => c * s.sum (λ x => (t x).sum (λ y => x * y))
/-- info: \sum_{i \in s}\text{id}(i) -/
#guard_msgs in #latex s.sum id



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

/-- info: (f : \mathbb{N} \to \mathbb{N}) \mapsto \left(\sum_{i \in s}f_{i}\right)^{2} -/
#guard_msgs in #latex λ (f : Nat → Nat) => (s.sum f)^2
