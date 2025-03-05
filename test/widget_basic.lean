import LeanTeX

set_option linter.unusedVariables false

open Lean

def a : Nat := 22

abbrev Real : Type := Nat
def Real.pi : Real := 3

open LeanTeX in
latex_pp_const_rule Real.pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "Real.pi"

def f : Nat → Nat → Nat := λ x y => x + y

def g : Unit → Nat := λ _ => 22

section

variable (b : Nat) (c : Nat → Real → Real) (x : Real)

#texify 1 + 2 + 3
#texify 1 + (2 + 3)
#texify (1 + 2) + 3
#texify b * (1 + 2 * 3 * 4 + 5) + 1
#texify f (Real.pi + a + f b 22) 2
#texify (1, (2, 3), a, Real.pi)
#texify Nat × Nat × Nat × Fin 37
#texify Nat × (n : Nat) × Fin n × Nat
#texify (⟨1, 1, 1⟩ : (n : Nat) × Fin n × Nat)
#texify ()
#texify g ()
#texify (λ (x : Nat) => x + 1)
#texify (λ (x y : Nat) => x + y + 1)
#texify (1 + 2) / 3
#texify (1 + 2/3)/4
#texify 1+1/(1+1/(1+1/(1+1/(1+1/(1+1)))))
#texify 2^2
#texify 4/2
#texify 2^(4/2)
#texify (1+2)^(3+4)
#texify 2^2^2
#texify (2^2)^2
#texify (1/2)^3
#texify Nat → Nat
#texify Prop
#texify (n : Nat) → Nat → Fin n
#texify (m n : Nat) → Fin (m + n)
#texify ∀ (n m : Nat), n < m → n < m + 1
#texify ∀ (n : Nat), 1 = 1
#texify {α : Type} → {β : Type} → {γ : Type} → [self : HAdd α β γ] → α → β → γ
#texify (α β : Type) → (f : α → β) → ∀ {x y : α}, f x = f y → x = y
#texify (p q r : Prop) → (p → q) → (p → q → r) → p → r
#texify (p₁ p₂ : Prop) → p₁ → (p₂ → p₁)
#texify (p p' : Prop) → p → (p' → p)
#texify c 1 x

#texify ∃ (n : Nat), 1 < n
#texify ∃ (n : Nat), ¬ n < 10
#texify ∃ (n : Nat), ¬ n = 0

def foo (n : Nat) : Prop := true
#texify Exists foo

#texify True ∧ True ∧ True
#texify ¬True ∨ True

variable (f_1 f_2 : Nat → Nat)

#texify (f_1 ∘ f_2) 37

#texify fun (_ : Nat) => 1

#texify 1 = 2

#texify ((1 = 1) = (2 = 2))

def Set (α : Type u) := α → Prop
instance : Membership α (Set α) := ⟨fun s x => s x⟩

variable (X : Type) (U : Set X) (x : X)

#texify x ∈ U

#texify x ∉ U

#texify Prod.mk 1

end

/-!
### Tactic
-/

example (x y : Nat) (h : x < y) : 2 * x < 2 * y := by
  texify
  sorry
