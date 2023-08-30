import LeanTeX.Builtins
import Std.Tactic.GuardMsgs

set_option linter.unusedVariables false

open Lean

def a : Nat := 22

abbrev Real : Type := Nat
def Real.pi : Real := 3

open LeanTeX in
latex_pp_const_rule Real.pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "Real.pi"

def f : Nat → Nat → Nat := λ x y => x + y

def g : Unit → Nat := λ _ => 22

variable (b : Nat) (c : Nat → Real → Real) (x : Real)

/-- info: 1 + 2 + 3 -/
#guard_msgs in #latex 1 + 2 + 3
/-- info: 1 + (2 + 3) -/
#guard_msgs in #latex 1 + (2 + 3)
/-- info: 1 + 2 + 3 -/
#guard_msgs in #latex (1 + 2) + 3
/-- info: b \cdot (1 + 2 \cdot 3 \cdot 4 + 5) + 1 -/
#guard_msgs in #latex b * (1 + 2 * 3 * 4 + 5) + 1
/-- info: \text{f}(\pi + \text{a} + \text{f}(b, 22), 2) -/
#guard_msgs in #latex f (Real.pi + a + f b 22) 2
/-- info: (1, (2, 3), \text{a}, \pi) -/
#guard_msgs in #latex (1, (2, 3), a, Real.pi)
/-- info: \mathbb{N} \times \mathbb{N} \times \mathbb{N} \times \mathbb{N}_{< 37} -/
#guard_msgs in #latex Nat × Nat × Nat × Fin 37
/-- info: \mathbb{N} \times (n : \mathbb{N}) \times \mathbb{N}_{< n} \times \mathbb{N} -/
#guard_msgs in #latex Nat × (n : Nat) × Fin n × Nat
/-- info: () -/
#guard_msgs in #latex ()
/-- info: \text{g}() -/
#guard_msgs in #latex g ()
/-- info: (x : \mathbb{N}) \mapsto x + 1 -/
#guard_msgs in #latex (λ (x : Nat) => x + 1)
/-- info: (x : \mathbb{N}, y : \mathbb{N}) \mapsto x + y + 1 -/
#guard_msgs in #latex (λ (x y : Nat) => x + y + 1)
/-- info: \frac{1 + 2}{3} -/
#guard_msgs in #latex (1 + 2) / 3
/-- info: \frac{1 + \tfrac{2}{3}}{4} -/
#guard_msgs in #latex (1 + 2/3)/4
/-- info: 1 + \frac{1}{1 + \tfrac{1}{1 + 1 / (1 + 1 / (1 + 1 / (1 + 1)))}} -/
#guard_msgs in #latex 1+1/(1+1/(1+1/(1+1/(1+1/(1+1)))))
/-- info: 2^{2} -/
#guard_msgs in #latex 2^2
/-- info: \frac{4}{2} -/
#guard_msgs in #latex 4/2
/-- info: 2^{4 / 2} -/
#guard_msgs in #latex 2^(4/2)
/-- info: (1 + 2)^{3 + 4} -/
#guard_msgs in #latex (1+2)^(3+4)
/-- info: 2^{2^{2}} -/
#guard_msgs in #latex 2^2^2
/-- info: (2^{2})^{2} -/
#guard_msgs in #latex (2^2)^2
/-- info: \left(\frac{1}{2}\right)^{3} -/
#guard_msgs in #latex (1/2)^3
/-- info: \mathbb{N} \to \mathbb{N} -/
#guard_msgs in #latex Nat → Nat
/-- info: \mathbf{Prop} -/
#guard_msgs in #latex Prop
/-- info: \prod_{n : \mathbb{N}} (\mathbb{N} \to \mathbb{N}_{< n}) -/
#guard_msgs in #latex (n : Nat) → Nat → Fin n
/-- info: \prod_{m : \mathbb{N}} \prod_{n : \mathbb{N}} \mathbb{N}_{< m + n} -/
#guard_msgs in #latex (m n : Nat) → Fin (m + n)
/-- info: \forall n : \mathbb{N},\ \forall m : \mathbb{N},\ n < m \implies n < m + 1 -/
#guard_msgs in #latex ∀ (n m : Nat), n < m → n < m + 1
/-- info: \forall n : \mathbb{N},\ 1 = 1 -/
#guard_msgs in #latex ∀ (n : Nat), 1 = 1
/-- info: \prod_{\alpha : \mathbf{Type}} \prod_{\beta : \mathbf{Type}} \prod_{\gamma : \mathbf{Type}} (\text{HAdd}_{\alpha, \beta, \gamma} \to (\alpha \to (\beta \to \gamma))) -/
#guard_msgs in #latex {α : Type} → {β : Type} → {γ : Type} → [self : HAdd α β γ] → α → β → γ
/-- info: \forall \alpha : \mathbf{Type},\ \forall \beta : \mathbf{Type},\ \forall f : \alpha \to \beta,\ \forall x : \alpha,\ \forall y : \alpha,\ f(x) = f(y) \implies x = y -/
#guard_msgs in #latex (α β : Type) → (f : α → β) → ∀ {x y : α}, f x = f y → x = y
/-- info: \forall p : \mathbf{Prop},\ \forall q : \mathbf{Prop},\ \forall r : \mathbf{Prop},\ (p \implies q) \implies ((p \implies (q \implies r)) \implies (p \implies r)) -/
#guard_msgs in #latex (p q r : Prop) → (p → q) → (p → q → r) → p → r
/-- info: \forall p_1 : \mathbf{Prop},\ \forall p_2 : \mathbf{Prop},\ p_1 \implies (p_2 \implies p_1) -/
#guard_msgs in #latex (p₁ p₂ : Prop) → p₁ → (p₂ → p₁)
/-- info: \forall p : \mathbf{Prop},\ \forall p' : \mathbf{Prop},\ p \implies (p' \implies p) -/
#guard_msgs in #latex (p p' : Prop) → p → (p' → p)
/-- info: c(1, x) -/
#guard_msgs in #latex c 1 x

/-- info: \exists n : \mathbb{N},\ 1 < n -/
#guard_msgs in #latex ∃ (n : Nat), 1 < n
/-- info: \exists n : \mathbb{N},\ \mathop{\neg} n < 10 -/
#guard_msgs in #latex ∃ (n : Nat), ¬ n < 10
/-- info: \exists n : \mathbb{N},\ n \neq 0 -/
#guard_msgs in #latex ∃ (n : Nat), ¬ n = 0

def foo (n : Nat) : Prop := true
/-- info: \exists x : \mathbb{N},\ \text{foo}(x) -/
#guard_msgs in #latex Exists foo

/-- info: \text{True} \mathrel{\mathrm{and}} \text{True} \mathrel{\mathrm{and}} \text{True} -/
#guard_msgs in #latex True ∧ True ∧ True
/-- info: \mathop{\neg} \text{True} \mathrel{\mathrm{or}} \text{True} -/
#guard_msgs in #latex ¬True ∨ True

variable (f1 f2 : Nat → Nat)

/-- info: (f1 \circ f2)(37) -/
#guard_msgs in #latex (f1 ∘ f2) 37

/-- info: (x : \mathbb{N}) \mapsto 1 -/
#guard_msgs in #latex fun (_ : Nat) => 1

/-- info: 1 = 2 -/
#guard_msgs in #latex 1 = 2

/-- info: 1 = 1 ⇔ 2 = 2 -/
#guard_msgs in #latex ((1 = 1) = (2 = 2))

def Set (α : Type u) := α → Prop
instance : Membership α (Set α) := ⟨fun x s => s x⟩

variable (X : Type) (U : Set X) (x : X)

/-- info: x \in U -/
#guard_msgs in #latex x ∈ U
