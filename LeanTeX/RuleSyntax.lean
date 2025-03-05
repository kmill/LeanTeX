import LeanTeX.Basic

namespace LeanTeX.RuleSyntax

open Lean Lean.Elab Lean.Elab.Command

syntax kindClause := atomic("(" &"kind") " := " ident ")"
syntax constClause := atomic("(" &"const") " := " ident ")"
syntax kindOrConstClause := kindClause <|> constClause
syntax paramKindsClause := atomic("(" &"paramKinds") " := " term ")"

/--
Convenient syntax for declaring new `latex_pp` pretty printers.

Some examples:
```
latex_pp_rules (kind := lit)
  | Expr.lit (Literal.natVal n) => return LatexData.atomString (toString n)

scoped latex_pp_rules (kind := lit)
  | Expr.lit (Literal.natVal n) => return LatexData.atomString (toString n)
```
Each can take attributes and `where` clauses.

For possible kinds, see the implementation of `LeanTeX.getExprKind`.

Note: `latex_pp_rules` adds a `| _ => failure` rule for you if there is no `| _ => ...` or `| e => ...` rule already.
-/
syntax (name := latex_pp_rules_syntax) (docComment)? (Parser.Term.attributes)? attrKind
  "latex_pp_rules" ppSpace kindClause
  Parser.Term.matchAltsWhereDecls : command

/--
Similar to `latex_pp_rules` but specialized to a particular constant.

Example:
```
latex_pp_const_rule Nat := (LatexData.atomString "\\mathbb{N}").maybeWithTooltip "Nat"
```
Note that the constant (here, `Nat`) is resolved with respect to the current scope.

This is roughly equivalent to
```
latex_pp_rules (kind := const.Nat)
  | _ => (LatexData.atomString "\\mathbb{N}").maybeWithTooltip "Nat"
```
(Except that it's currently not allowed to do a catch-all pattern with `latex_pp_rules`.)
-/
syntax (name := latex_pp_const_syntax) (docComment)? (Parser.Term.attributes)? attrKind
  "latex_pp_const_rule" ident " := " ppHardLineUnlessUngrouped term (Parser.Term.whereDecls)? : command

/--
Convenient syntax for defining new `latex_pp_app` handlers.

The syntax
```
latex_pp_app_rules (kind := k) (paramKind := pkinds)
  | f, #[arg1, arg2, ...] => ...
```
adds a new handler with `@[latex_pp_app k]`. The `(paramKind := ...)` is optional.

The variant
```
latex_pp_app_rules (const := name) ...
```
resolves `name` in the current scope and does `latex_pp_app_rules (kind := const.name) ...`.

Note: adds a `| _, _ => failure` rule for you if there is no `| _, _ => ...` or `| e, args => ...` rule already.
-/
syntax (name := latex_pp_app_rules_syntax) (docComment)? (Parser.Term.attributes)? attrKind
  "latex_pp_app_rules" ppSpace kindOrConstClause ppSpace (paramKindsClause)?
  Parser.Term.matchAltsWhereDecls : command


/-- Process a `kindOrConstClause`, returning the resolved kind as well as the kind as an `Ident`. -/
def processKindOrConst (c : TSyntax ``kindOrConstClause) : CommandElabM (Name × Ident) := do
  match c with
  | `(kindOrConstClause| (const := $id)) =>
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let kind := `const ++ name
    return (kind, mkIdentFrom id kind)
  | `(kindOrConstClause| (kind := $id)) =>
    return (id.getId, id)
  | _ => throwUnsupportedSyntax

/-- Process a `paramKindsClause`, returning its term. Returns `_` if none. -/
def processParamKinds (c? : Option (TSyntax ``paramKindsClause)) : CommandElabM Term := do
  if let some c := c? then
    match c with
    | `(paramKindsClause| (paramKinds := $t)) => return t
    | _ => throwUnsupportedSyntax
  else
    `(_)

@[command_elab latex_pp_rules_syntax] def elab_latex_pp_rules : CommandElab :=
  adaptExpander fun
  | `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
                latex_pp_rules (kind := $kind:ident) $alts:matchAlt* $[$whereClause?:whereDecls]?) => do
    let alts ← maybeAddFailureRule alts
    let body ← `(term| fun $alts:matchAlt*)
    let body' ← liftMacroM <| Term.expandWhereDeclsOpt (mkOptionalNode whereClause?) body
    let ppAttr ← `(Lean.Parser.Term.attrInstance| $attrKind? latex_pp $kind)
    let attrs := attrs?.map (·.getElems) |>.getD #[] |>.push ppAttr
    `(command| $[$doc?:docComment]? @[$attrs,*]
                aux_def latex_pp_rule : LatexPrinter := $(TSyntax.mk body'))
  | _ => Elab.throwUnsupportedSyntax
where
  -- TODO: would be nice if we could use `no_error_if_unused%`
  maybeAddFailureRule (alts : TSyntaxArray ``Parser.Term.matchAlt) :
      CommandElabM (TSyntaxArray ``Parser.Term.matchAlt) := do
    match alts.back?.getD default with
    | `(Parser.Term.matchAltExpr| | _ => $_)
    | `(Parser.Term.matchAltExpr| | $_:ident => $_) => return alts
    | _ => return alts.push <| ← `(Parser.Term.matchAltExpr| | _ => failure)

@[command_elab latex_pp_const_syntax] def elab_latex_pp_const_rule : CommandElab :=
  adaptExpander fun
  | `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
                latex_pp_const_rule $name:ident := $body:term $[$whereClause?:whereDecls]?) => do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
    let kind := mkIdentFrom name (`const ++ c)
    let ppAttr ← `(Lean.Parser.Term.attrInstance|$attrKind? latex_pp $kind)
    let attrs := attrs?.map (·.getElems) |>.getD #[] |>.push ppAttr
    let body' ← liftMacroM <| Term.expandWhereDeclsOpt (mkOptionalNode whereClause?) body
    `(command| $[$doc?:docComment]? @[$attrs,*]
                aux_def latex_pp_rule : LatexPrinter := fun _ => $(TSyntax.mk body'))
  | _ => Elab.throwUnsupportedSyntax

@[command_elab latex_pp_app_rules_syntax] def elab_latex_app_pp_rules : CommandElab :=
  adaptExpander fun
  | `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
                latex_pp_app_rules $kc:kindOrConstClause $[$pk?]? $alts:matchAlt* $[$whereClause?:whereDecls]?) => do
    let (_, kind) ← processKindOrConst kc
    let pkinds ← processParamKinds pk?
    let alts ← maybeAddFailureRule alts
    let body ← `(term| match f, args with $alts:matchAlt*)
    let body ← liftMacroM <| TSyntax.mk <$> Term.expandWhereDeclsOpt (mkOptionalNode whereClause?) body
    let body ← `(term| fun | f, args, $pkinds => $body)
    let ppAttr ← `(Lean.Parser.Term.attrInstance|$attrKind? latex_pp_app $kind)
    let attrs := attrs?.map (·.getElems) |>.getD #[] |>.push ppAttr
    `(command| $[$doc?:docComment]? @[$attrs,*]
                aux_def latex_pp_rule : LatexAppPrinter := $body)
  | _ => Elab.throwUnsupportedSyntax
where
  isCatchAllPatt (t : Term) : Bool :=
    match t with
    | `(_) | `($_:ident) => true
    | _ => false
  -- TODO: would be nice if we could use `no_error_if_unused%`
  maybeAddFailureRule (alts : TSyntaxArray ``Parser.Term.matchAlt) :
      CommandElabM (TSyntaxArray ``Parser.Term.matchAlt) := do
    let fail ← `(Parser.Term.matchAltExpr| | _, _ => failure)
    match alts.back?.getD default with
    | `(Parser.Term.matchAltExpr| | $x, $y => $_) =>
      if isCatchAllPatt x && isCatchAllPatt y then
        return alts
      else
        return alts.push fail
    | _ => return alts.push fail
