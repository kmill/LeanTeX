import Lean.Data
import LeanTeX.LatexChar
import LeanTeX.RuleSyntax
import LeanTeX.MkAppN

/-! # Builtin LaTeX pretty printers

These are pretty printer definitions for the system defined in `LeanTeX.Basic`.

-/

open Lean
open scoped MkAppNMacro

/-- Replace common unicode characters by their TeX representation. For instance
`α` will be replaced by `\alpha`. -/
partial def String.toLatex (s : String) : String :=
  match (s.split ('_' == ·)).map (fun part => part.foldl (λ s' t => s' ++ t.toLatex) "") with
  | x :: xs@(_ :: _) =>
    if x.isEmpty then
      "\\_" ++ ("_".intercalate xs).toLatex
    else
      x ++ s!"_\{{"_".intercalate xs}}"
  | xs => "_".intercalate xs

/-- Convert a `Name` to a `String` and then use `String.toLatex` to replace common
unicode characters by LaTeX commands. -/
def Lean.Name.toLatex (n : Name) : String := (toString n).toLatex

/-- Give a LaTeX-suitable representation of the local variable. -/
def Lean.FVarId.toLatex (fvarid : FVarId) : MetaM String :=
  try return (← fvarid.getDecl).userName.simpMacroScopes.toLatex
  catch _ =>
    -- loose free variable, use internal name
    pure s!"\\operatorname\{FVar}[\\text\{{fvarid.name}}]"

namespace LeanTeX

/-- By default, strip off annotations. -/
latex_pp_rules (kind := mdata)
  | Expr.mdata _ e => latexPP e

/-- `LatexPrinter` for free variables. -/
latex_pp_rules (kind := fvar)
  | Expr.fvar fvarId => return LatexData.atomString (← fvarId.toLatex) 

namespace Extra
/-- `LatexPrinter` for metavariables. These print using the `userName` prefixed with "?".
To use, do `open scoped Latex.Extra`. -/
scoped latex_pp_rules (kind := mvar)
  | Expr.mvar mvarId => do
    let name := "?" ++ (← mvarId.getDecl).userName.toLatex
    return LatexData.atomString name
end Extra

/-- `LatexPrinter` for loose bound variables. Loose bound variables should not appear, so the default implementation is to fail. -/
latex_pp_rules (kind := bvar)
  | _ => failure

/-- `LatexPrinter` for literals. Currently only `ℕ` literals are handled. -/
latex_pp_rules (kind := lit)
  | Expr.lit (Literal.natVal n) => return LatexData.atomString (toString n)

/-- Default `LatexPrinter` for constants. Specific constants can have more specialized printers.
See `latex_pp_const_rule`. -/
latex_pp_rules (kind := const)
  | Expr.const c _ => return LatexData.atomString (← maybeWithTooltip s!"\\text\{{c}}" c.toString)

/-- Pretty print type universes, printing all `Type _` as `Type`. `Sort` is the union of `Prop` and `Type`. -/
latex_pp_rules (kind := sort)
  | Expr.sort u => do
    let u ← Meta.normalizeLevel u
    match u with
    | .zero   => return LatexData.atomString "\\mathbf{Prop}"
    | .succ _ => return LatexData.atomString "\\mathbf{Type}"
    | _       => return LatexData.atomString "\\mathbf{Sort}"

private partial def collectLambdaArgs : Expr → Array (Name × LatexData) → LatexPrinterM (Array (Name × LatexData) × LatexData)
  | e@(.lam ..), args =>
    withBindingBodyUnusedName e fun name body => do
      collectLambdaArgs body (args.push (name, ← latexPP e.bindingDomain!))
  | e, args => do return (args, ← latexPP e)

/-- `LatexPrinter` for `λ`-abstractions. For instance `λ x : ℝ => x^2` is rendered as `(x : ℝ) ↦ x^2`. -/
latex_pp_rules (kind := lam) | e => do
  let (args, body) ← collectLambdaArgs e #[]
  let pargs := LatexData.intercalate ", " <| args.map (λ (name, type) => LatexData.ofString name.toLatex ++ " : " ++ type)
  return pargs.parens ++ LatexData.nonAssocOp " \\mapsto " 0 ++ body

/-- Simple implementation. Doesn't collect anything at all, compared to `pp_lam`. -/
latex_pp_rules (kind := forallE) | e => do
  let prop? ← try Meta.isProp e catch _ => pure false
  let arrow? := e.isArrow
  let domProp? ← try Meta.isProp e.bindingDomain! catch _ => pure false

  if prop? then
    if arrow? ∧ domProp? then
      -- implication
      let pdom ← latexPP e.bindingDomain!
      let pbody ← latexPP e.bindingBody!
      let assoc := if (← read).implicationAssoc then LatexData.rightAssocOp else LatexData.nonAssocOp
      return pdom.protectRight 30 ++ assoc " \\implies " 30 ++ pbody.protectLeft 30
    else
      -- forall
      let pdom ← latexPP e.bindingDomain!
      withBindingBodyUnusedName e fun name body => do
        let pbody ← latexPP body
        let binder := if (← read).omitBinders then LatexData.atomString "" else " : " ++ pdom.resetBP .Infinity .Infinity
        let pall := s!"\\forall {name.toLatex}" ++ binder ++ ",\\ " ++ pbody
        return pall |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 0)
  else
    if arrow? then
      -- function
      let pdom ← latexPP e.bindingDomain!
      let pbody ← latexPP e.bindingBody!
      return pdom.protectRight 30 ++ LatexData.nonAssocOp " \\to " 30 ++ pbody.protectLeft 30
    else
      -- pi
      let pdom ← withExtraSmallness 2 <| latexPP e.bindingDomain!
      withBindingBodyUnusedName e fun name body => do
        let pbody ← latexPP body
        let binder := if (← read).omitBinders then LatexData.atomString "" else " : " ++ pdom.resetBP .Infinity .Infinity
        let ppi := s!"\\prod_\{{name.toLatex}" ++ binder ++ "} " ++ pbody.protect 30
        return ppi |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .Assoc 30)

/-- The binding power of function applications. -/
def funAppBP : Nat := 1024

/-- Whether the type is for an indexed family of types, propositions, or sets. -/
partial def type_is_indexed_family : Expr → MetaM Bool
| .sort (.succ _) => return true
| .app (.const `Set _) _ | .app (.const `Finset _) _ => return true
| e@(.forallE ..) => do
  Meta.withLocalDecl e.bindingName! e.binderInfo e.bindingDomain! fun fvar =>
    type_is_indexed_family (e.bindingBody!.instantiate1 fvar)
| _ => return false

/-- The default function application printer finds the longest prefix that can be handled by a
`latex_pp_app` handler. -/
latex_pp_rules (kind := app) | e => do
  let f := e.getAppFn
  let args := e.getAppArgs
  let pkinds ← getParamKinds e
  let kind := getExprKind f
  for i in [0 : args.size] do
    try
      let f' ← latexPPAppFor kind f (args.extract 0 (args.size - i)) pkinds
      return ← pp_rem f'
                (mkAppN f <| args.extract 0 (args.size - i)) (args.extract (args.size - i) args.size)
                (pkinds.extract (args.size - i) pkinds.size)
    catch _ => pure ()
  pp_rem (← latexPP f) f args pkinds
where
  pp_rem (f' : LatexData) (f : Expr) (args : Array Expr) (pkinds : Array ParamKind) : LatexPrinterM LatexData := do
    -- TODO handle optional arguments
    if args.size == 0 then
      return f'
    let mut is_fam := false
    if (← read).familySubscripts then
      try
        is_fam ← type_is_indexed_family (← Meta.inferType f)
      catch _ => pure ()
    let mut pargs : Array LatexData := #[]
    for arg in args, pkind in pkinds do
      if pkind.bInfo.isExplicit then
        pargs := pargs.push (← withExtraSmallness (if is_fam then 2 else 0) <| latexPP arg)
    if is_fam then
      return f'.toAtom.sub <| LatexData.intercalate ", " pargs
    else
      return f'.protectRight funAppBP ++ (LatexData.intercalate ", " pargs).parens |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)

/-- Special case for a function applied to `()`. -/
latex_pp_rules (kind := app)
  | .app f (.const `Unit.unit _) => do
    let res ← latexPP f
    return res.protectRight funAppBP ++ "()" |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)

/-- `@OfNat.ofNat _ n _` ~> `n` -/
latex_pp_app_rules (const := OfNat.ofNat)
  | _, #[_, (.lit (.natVal n)), _] => return LatexData.atomString (toString n)

-- FIXME: This doesn't handle bounded exists such as `∃ δ > 0, P δ` which should be special-cased.
latex_pp_app_rules (const := Exists)
  | _, #[α, p] => do
    let pdom ← latexPP α
    withBindingBodyUnusedName' p `x fun name body => do
      let pbody ← latexPP body
      let mut binder : LatexData := .atomString name.toLatex
      if (← read).omitBinders then
        binder ← binder.maybeWithTooltip s!"in \\({pdom.latex.1}\\)"
      else
        binder := binder ++ " : " ++ pdom.resetBP .Infinity .Infinity
      let pex := s!"\\exists " ++ binder ++ ",\\ " ++ pbody
      return pex |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 0)

/-- Factory function for printers for binary operations. Only checks properties of the
arguments list -- it is up to users of this to make sure the correct function is being applied.

- `numArgs` is the number of arguments for the binary operation. 
- `lhsIdx` is the index into the arguments list for the LHS.
- `rhsIdx` is the index into the arguments list for the RHS. -/
def basicBinOpPrinter (op : String) (bp : Nat) (assoc : Associativity) (numArgs : Nat)
    (lhsIdx := numArgs - 2) (rhsIdx := numArgs - 1) : LatexAppPrinter
  | _, args, _ => do
    if args.size != numArgs then
      failure
    let a ← latexPP args[lhsIdx]!
    let b ← latexPP args[rhsIdx]!
    return a.protectRight bp ++ LatexData.binOp op assoc bp ++ b.protectLeft bp

/--
Defines a `latex_pp_app` for a given binary operator. Assumes the last two arguments to the
operator are the LHS and RHS of the operator.
```
def_latex_binop OpName "latex" precedence associativity
```
Precedence is a `Nat`. Associativity is a `Latex.Associativity`. The OpName is a name
resolved in the current scope.
-/
syntax (name := latex_binop_syntax) (docComment)? (Parser.Term.attributes)? attrKind
  "def_latex_binop" ident term:arg term:arg term:arg : command

open Meta Lean.Elab Lean.Elab.Command in
@[command_elab latex_binop_syntax] def elab_latex_binop : CommandElab :=
  adaptExpander fun
  | `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
                def_latex_binop $name:ident $latex:term $prec:term $assoc:term) => do
    let c ← resolveGlobalConstNoOverloadWithInfo name
    let t ← Lean.mkConstWithLevelParams c
    let arity ← liftTermElabM <| withTransparency TransparencyMode.default do
                  forallTelescopeReducing (← inferType t) fun args _ => pure args.size
    let kind := mkIdentFrom name (`const ++ c)
    `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
               latex_pp_app_rules (kind := $kind) (paramKinds := pkinds)
                | f, args =>
                    (basicBinOpPrinter $latex $prec $assoc $(quote arity)) f args pkinds)
  | _ => Elab.throwUnsupportedSyntax

def_latex_binop And " \\mathrel{\\mathrm{and}} " 35 .right
def_latex_binop Or " \\mathrel{\\mathrm{or}} " 30 .right

latex_pp_app_rules (const := Not)
  | _, #[mkAppN (.const ``Eq [u]) #[α, x, y]] =>
    -- Not-equals as neq
    latexPP <| mkAppN (.const ``Ne [u]) #[α, x, y]
  | _, #[mkAppN (.const ``Membership.mem _) #[_, _, _, x, y]] => do
    let a ← latexPP x
    let b ← latexPP y
    return a.protectRight 50 ++ LatexData.nonAssocOp " \\notin " 50 ++ b.protectLeft 50
  | _, #[p] => do
    let p ← latexPP p
    return LatexData.rightAssocOp "\\mathop{\\neg} " 40 ++ p.protectLeft 40

def_latex_binop Eq " = " 50 .none
def_latex_binop Iff " ⇔ " 20 .none
def_latex_binop Ne " \\neq " 50 .none
def_latex_binop LT.lt " < " 50 .none
def_latex_binop LE.le " \\leq " 50 .none
def_latex_binop GT.gt " > " 50 .none
def_latex_binop GE.ge " \\geq " 50 .none

def_latex_binop HAdd.hAdd " + " 65 .left
def_latex_binop HSub.hSub " - " 65 .left
def_latex_binop HMul.hMul " \\cdot " 70 .left

/-- Render equalities between propositions as an iff. -/
latex_pp_app_rules (const := Eq)
  | _, #[_, p, .const `True _] => do
    unless ← Meta.isProp p do failure
    latexPP p
  | _, #[_, p, q] => do
    unless ← Meta.isProp p do failure
    let a ← latexPP p
    let b ← latexPP q
    return a.protectRight 20 ++ LatexData.binOp " ⇔ " .none 20 ++ b.protectLeft 20

latex_pp_app_rules (const := Neg.neg)
  | _, #[_, _, x] => do
    let x ← latexPP x
    return LatexData.rightAssocOp " - " 75 ++ x.protectLeft 75

latex_pp_app_rules (const := Nat.succ)
  | _, #[a] => do
    let a ← latexPP a
    return a.protectRight 65 ++ LatexData.leftAssocOp " + " 65
      ++ (← LatexData.atomString "1" |>.maybeWithTooltip "Nat.succ").protectLeft 65

latex_pp_app_rules (const := Membership.mem)
  | _, #[_, _, _, a, b] => do
    let a ← latexPP a
    let b ← latexPP b
    return a.protectRight 50 ++ LatexData.nonAssocOp " \\in " 50 ++ b.protectLeft 50

-- Note: `HasSubset.Subset` is not in scope here
latex_pp_app_rules (kind := const.HasSubset.Subset)
  | _, #[_, _, a, b] => do
    let a ← latexPP a
    let b ← latexPP b
    return a.protectRight 50 ++ LatexData.nonAssocOp " \\subseteq " 50 ++ b.protectLeft 50

@[latex_pp_app const.Union.union] def pp_Union := basicBinOpPrinter " \\cup " 65 .left 4
@[latex_pp_app const.Inter.inter] def pp_Inter := basicBinOpPrinter " \\cap " 70 .left 4

/-- This renders `Set.image f X` as `f[X]`, which is a reasonably common notation for set image. -/
latex_pp_app_rules (kind := const.Set.image)
  | _, #[_, _, f, X] => do
    let f ← latexPP f
    let X ← latexPP X
    return ← f.protectRight funAppBP ++ X.brackets |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)
      |>.maybeWithTooltip s!"image of \\({X.latex.1}\\) under \\({f.latex.1}\\)"

/-- Default division: use division slash -/
def_latex_binop HDiv.hDiv " / " 70 .left

/-- Fancy division: use frac or tfrac if things aren't too small. -/
latex_pp_app_rules (const := HDiv.hDiv)
  | _, #[_, _, _, _, a, b] => do
    let frac ←
      match (← read).smallness with
        | 0 => pure LatexData.frac
        | 1 => pure LatexData.tfrac
        | _ => failure
    let a ← withExtraSmallness 1 <| latexPP a
    let b ← withExtraSmallness 1 <| latexPP b
    return frac a b

/-- Powers. -/
latex_pp_app_rules (const := HPow.hPow)
  | _, #[_, _, _, _, a, b] => do
    let a ← latexPP a
    let b ← withExtraSmallness 2 <| latexPP b
    return a.sup b

/-- `LatexPrinter` for `() : Unit`. Hopefully this won't appear too much, especially since
there is a specific application printer for functions applied to `()`. -/
latex_pp_const_rule Unit.unit := return LatexData.atomString "()"

/-- Represent elements of a product as tuples, using Lean-style right-associativity rules. -/
latex_pp_app_rules (const := Prod.mk)
  | _, #[_, _, a, b] => do
    let args := recogProd #[a] b
    let pp ← args.mapM latexPP
    return (LatexData.intercalate ", " pp).parens
where recogProd (currArgs : Array Expr) (e : Expr) : Array Expr :=
  match e with
  | mkAppN (.const `Prod.mk _) #[_, _, a, b] =>
    recogProd (currArgs.push a) b
  | _ => currArgs.push e

/-- `LatexPrinter` for products of types. -/
def_latex_binop Prod " \\times " 35 .right

/-- `LatexPrinter` for composition of functions. -/
latex_pp_app_rules (const := Function.comp)
  | _, #[_, _, _, f, g] => do
    let a ← latexPP f
    let b ← latexPP g
    let op ← LeanTeX.maybeWithTooltip "\\circ" "Function.comp"
    return a.protectRight 90 ++ LatexData.rightAssocOp s!" {op} " 90 ++ b.protectLeft 90

/-- Display sigma notation like `(i : α) × f(i)` -/
latex_pp_app_rules (const := Sigma)
  | _, #[α, f] => do
    let pα ← withExtraSmallness 2 <| latexPP α
    withBindingBodyUnusedName' f `i fun name body => do
      let pbind : LatexData := LatexData.parens (name.toLatex ++ " : " ++ pα)
      let pbody ← latexPP body
      return pbind ++ LatexData.rightAssocOp " \\times " 35 ++ pbody.protectLeft 34

/-- `LatexPrinter` for the type of natural numbers.-/
latex_pp_const_rule Nat := (LatexData.atomString "\\mathbb{N}").maybeWithTooltip "Nat"

latex_pp_const_rule Nat.zero := (LatexData.atomString "0").maybeWithTooltip "Nat.zero"

/-- An experiment: use a subscript for an argument. Represents `Fin n` as `\mathbb{N}_{<n}` -/
latex_pp_app_rules (const := Fin)
  | _, #[n] => do
    let n ← withExtraSmallness 2 <| latexPP n
    return (← LatexData.atomString "\\mathbb{N}" |>.maybeWithTooltip "Fin").sub ("< " ++ n)

latex_pp_app_rules (kind := const.Finset.prod)
| _, #[_α, _β, _inst, s, f] => do
  let set ← withExtraSmallness 2 <| latexPP s
  withBindingBodyUnusedName' f `i fun name body => do
    let pbody ← latexPP body
    let pbody := pbody.protectLeft 66
    let psum := (← (LatexData.atomString "\\prod" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ set) |>.maybeWithTooltip "Finset.prod") ++ pbody
    return psum |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

latex_pp_app_rules (kind := const.Finset.sum)
  | _, #[_α, _β, _inst, s, f] => do
    let set ← withExtraSmallness 2 <| latexPP s
    withBindingBodyUnusedName' f `i fun name body => do
      let pbody ← latexPP body
      let pbody := pbody.protectLeft 66
      let psum := (← (LatexData.atomString "\\sum" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ set) |>.maybeWithTooltip "Finset.sum") ++ pbody
      return psum |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

latex_pp_app_rules (kind := const.EmptyCollection.emptyCollection)
| _, #[_α, _inst] => pure <| LatexData.atomString "\\varnothing"

end LeanTeX
