import Lean

/-! # Elaborator for `mkAppN f #[...]`

Defines a macro that expands `mkAppN f #[...]` to just use `Expr.app`,
which allows it to be used in patterns.

Use `open scoped MkAppNMacro` to enable. -/

open Lean Meta

namespace MkAppNMacro

@[inherit_doc mkAppN]
scoped macro_rules
  | `(mkAppN $f #[$xs,*]) =>
    (xs.getElems.foldlM (fun x e => `(Expr.app $x $e)) f : MacroM Term)
