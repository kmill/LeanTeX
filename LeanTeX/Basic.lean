import Lean.Data
import Lean.KeyedDeclsAttribute
import Lean.PrettyPrinter
import Lean.Parser
import Lean.Elab.Command
import Lean.Elab.AuxDef
import LeanTeX.Defs

/-! # LaTeX pretty printer for math expressions

This module sets up the basic system for transforming a given `Lean.Expr` into
a human-readable LaTeX expression. Unlike the usual Lean pretty printer, we do not aim for
total computer-interpretable accuracy -- the resulting LaTeX expressions should be at a
similar level of detail to human-written mathematics, where a human's mental elaboratation
process could fill in the missing details (that is, the output is permitted to be ambiguous
in ways that mathematicians are accustomed to).

The function `LeanTeX.latex` is the main entry point for the pretty printer.

The specific pretty printers are in the `LeanTeX.Builtins` module. We use the attributes
system to record the pretty printers, and one can't apply an attribute in the same module in
which it was defined.

There are two kinds of pretty printers that can be registered: the generic one uses the attribute
`latex_pp` and there is a specialized one `latex_pp_app` for function applications. Those attributes
are keyed by "kind" which is a `Lean.Name`. When pretty-printing an `Expr`, those kinds are compared to
one computed from the expression by `LeanTeX.getExprKind`. The hierarchical nature of names is used here
to first try the most specific pretty-printer, matching the full kind, and then, in case of failure,
try to remove the last name part and iterate, see `LeanTeX.latexPPFor`.

The fact that function applications use pretty-printers registered using the attribute `latex_pp_app`
cannot be seen in this file, this happens in the function application builtin pretty-printer
from the `Builtins` file.

One complexity in the design is that human-written mathematics is a 2D notation. A simple
precedence-level-based system does not work. For example, in `(a/b)^c` as
`(\tfrac{a}{b})^c`, we have the parentheses there *not* because exponentiation has higher
precedence than division, but instead because in the 2D layout exponentiation would be
otherwise indistinguishable from being an exponent on `a`. Pieces of LaTeX code are stored in
objects with type `LeanTeX.LatexData`. This type is has two constructors: `Atom` for pieces that
can be decorated with subscripts or superscripts without parentheses and `Row` for pieces that
require parentheses. In the `Row` case, the `LatexData` has binding powers on both sides, left and right.
Those represent how resistant an expression is to be broken up if it is inserted into another expression.
This resistance is used when deciding whether parentheses should be used.
-/

open Lean

namespace LeanTeX

/-- A `LatexPrinter` is the type of a function that pretty prints expressions.
These are registered using the `latex_pp` attribute. -/
abbrev LatexPrinter := Expr → LatexPrinterM LatexData

/-- `latex_pp` attribute registration function. -/
unsafe def mkLatexPPAttribute : IO (KeyedDeclsAttribute LatexPrinter) :=
  KeyedDeclsAttribute.init {
    name  := `latex_pp
    descr := "Register a LaTeX pretty printer for a kind of an expression.
See `LeanTeX.getExprKind` for the possible kinds.

[latex_pp k] registers a `TeXPP.TeXPrinter` for kind `k`.",
    valueTypeName := `LeanTeX.LatexPrinter
    evalKey := fun _ stx => do
      let id := (← Attribute.Builtin.getIdent stx).getId
      if id.isAnonymous then
        throwError "Anonymous name"
      return id
  } `LatexPrinter.latexPPAttribute

@[init mkLatexPPAttribute] opaque latexPPAttribute : KeyedDeclsAttribute LatexPrinter

/-- Structure representing the data for a parameter. Used, for example, in getting the list
of the types of arguments to a function. -/
structure ParamKind where
  name        : Name
  type        : Expr
  bInfo       : BinderInfo
  defVal      : Option Expr := none
  isAutoParam : Bool := false
  deriving Repr, Inhabited

/-- Checks whether the given parameter is explicit, not autoparam and has no default value. -/
def ParamKind.isRegularExplicit (param : ParamKind) : Bool :=
  param.bInfo.isExplicit && !param.isAutoParam && param.defVal.isNone

/-- Return array whose elements correspond to parameters of `e`. -/
partial def getParamKinds (e : Expr) : MetaM (Array ParamKind) := do
  try
    Meta.withTransparency Meta.TransparencyMode.all <|
      forallTelescopeArgs e.getAppFn e.getAppArgs fun params _ => do
        params.mapM fun param => do
          let l ← param.fvarId!.getDecl
          pure { name := l.userName, type := l.type,
                 bInfo := l.binderInfo, defVal := l.type.getOptParamDefault?, isAutoParam := l.type.isAutoParam }
  catch _ => pure #[] -- expr might be nonsensical
where
  forallTelescopeArgs f args k := do
    Meta.forallBoundedTelescope (← Meta.inferType f) args.size fun xs b =>
      if xs.isEmpty || xs.size == args.size then
        -- we still want to consider optParams
        Meta.forallTelescopeReducing b fun ys b => k (xs ++ ys) b
      else
        forallTelescopeArgs (mkAppN f $ args.shrink xs.size) (args.extract xs.size args.size) fun ys b =>
          k (xs ++ ys) b

/-- Latex printers specifically for applications. Takes the function, its arguments, and
an array describing the corresponding function parameters. -/
abbrev LatexAppPrinter := Expr → Array Expr → Array ParamKind → LatexPrinterM LatexData

/-- `latex_pp_app` attribute registration function. -/
unsafe def mkLatexPPAppAttribute : IO (KeyedDeclsAttribute LatexAppPrinter) :=
  KeyedDeclsAttribute.init {
    name  := `latex_pp_app
    descr := "Register a LaTeX pretty printer for applications of a given constant.

[latex_pp_app const.c] registers a `LatexAppPrinter` for applications of the constant `c`.
[latex_pp_app app] registers a `LatexAppPrinter` for non-specific applications.",
    valueTypeName := `LeanTeX.LatexAppPrinter
    evalKey := fun _ stx => do
      let id := (← Attribute.Builtin.getIdent stx).getId
      if id.isAnonymous then
        throwError "Anonymous name"
      return id
  } `LatexPrinter.latexPPAppAttribute

@[init mkLatexPPAppAttribute] opaque latexPPAppAttribute : KeyedDeclsAttribute LatexAppPrinter

/-- Adds primes or indices to a name. -/
private def appendIndexOrPrimeAfter (n : Name) (idx : Nat) : Name :=
  n.modifyBase fun
    | .str p s => Name.mkStr p <| if h : idx < alts.size then s ++ alts[idx] else s ++ "_" ++ toString (idx + 1)
    | n       => Name.mkStr n ("_" ++ toString idx)
  where alts : Array String := #["'", "''", "'''"]

/-- Get a fresh name based on the suggested name that doesn't shadow anything in `body`.
(Stolen from the Lean pretty printer.) Also makes sure the name is not in the `avoidNames` list. -/
partial def getUnusedName (suggestion : Name) (body : Expr) : LatexPrinterM Name := do
  -- Use a nicer binder name than `[anonymous]`.
  let suggestion := if suggestion.isAnonymous then `a else suggestion
  let suggestion := dropNum suggestion.simpMacroScopes
  let lctx ← getLCtx
  let avoidNames := (← read).avoidNames
  if (← read).allowShadowing && !avoidNames.contains suggestion && !bodyUsesSuggestion lctx suggestion then -- safe shadowing
    return suggestion
  let rec loop (i : Nat) : Name :=
    let curr := appendIndexOrPrimeAfter suggestion i
    if lctx.usesUserName curr || avoidNames.contains curr then loop (i + 1)
    else curr
  return if lctx.usesUserName suggestion then loop 0
         else suggestion
where
  bodyUsesSuggestion (lctx : LocalContext) (suggestion' : Name) : Bool :=
    Option.isSome <| body.find? fun
      | Expr.fvar fvarId =>
        match lctx.find? fvarId with
        | none      => false
        | some decl => decl.userName == suggestion'
      | _ => false
  dropNum : Name → Name
    | .num base _ => base
    | name => name

/-- Given an `Expr` that is a `.forallE` or `.lam`, execute the given `d` in the context of a
local declaration. The function `d` is provided the name of the new local and its type.  -/
def withBindingBodyUnusedName (e : Expr) (d : Name → Expr → LatexPrinterM α) : LatexPrinterM α := do
  let n ← getUnusedName e.bindingName! e.bindingBody!
  Meta.withLocalDecl n e.binderInfo e.bindingDomain! fun fvar =>
    d n (e.bindingBody!.instantiate1 fvar)

/-- Given an expression that is a function, ensure it is an `Expr.lam` by doing 1-variable
eta expansion as needed.
If provided, the `suggestion?` argument gives the name for the new argument to the lambda, and otherwise
the name comes from the function's pi type. -/
def ensureLam (e : Expr) (suggestion? : Option Name) : MetaM Expr := do
  if e.isLambda then
    return e
  else
    let ty ← Meta.whnf (← Meta.inferType e)
    guard ty.isForall
    Meta.withLocalDeclD (suggestion?.getD ty.bindingName!) ty.bindingDomain! fun fvar =>
      Meta.mkLambdaFVars #[fvar] (.app e fvar)

/-- Given an `Expr` that is a function, use `ensureLam` to ensure it is a lambda expression
and then execute the given `d` using `withBindingBodyUnusedName`. -/
def withBindingBodyUnusedName' (e : Expr) (suggestion? : Option Name) (d : Name → Expr → LatexPrinterM α) : LatexPrinterM α := do
  let e ← ensureLam e suggestion?
  withBindingBodyUnusedName e d

/-- Get a description of the constructor of the expression as a `Name`.
Used as a key for the `latex_pp` attribute. -/
def getExprKind : Expr → Name
  | Expr.bvar _          => `bvar
  | Expr.fvar _          => `fvar
  | Expr.mvar _          => `mvar
  | Expr.sort _          => `sort
  | Expr.const c _       => `const ++ c
  | Expr.app fn _        =>
    match fn.getAppFn with
      | Expr.const c _   => `app ++ c
      | _                => `app
  | Expr.lam _ _ _ _     => `lam
  | Expr.forallE _ _ _ _ => `forallE
  | Expr.letE _ _ _ _ _  => `letE
  | Expr.lit _           => `lit
  | Expr.mdata m _       =>
    match m.entries with
    | [(key, _)] => `mdata ++ key
    | _   => `mdata
  | Expr.proj _ _ _      => `proj

/-- The failsafe Latex pretty printer, which just runs the usual Lean pretty printer and wraps it
in some LaTeX to make it clear this was not handled. Mainly used for debugging purposes. -/
def defaultLatexPP (e : Expr) : LatexPrinterM LatexData := do
  let f ← PrettyPrinter.ppExpr e
  -- TODO try to do `Format` -> reasonable latex.
  return LatexData.ofString <| s!"\\operatorname\{Lean}\\left[\\text\{{f}}\\right]"

/-- For the given kind (as in `getExprKind`), run the associated pretty printer.

The general algorithm for the specified `kind`:
1. Find the first handler (with respect to reverse-definition order) with
   attribute `latex_pp kind` that does not fail. If one exists, we're done.
2. If it's different, use `Name.getRoot kind` as the new `kind` and try again.
3. Otherwise fail. -/
partial def latexPPFor (e : Expr) (kind : Name) : LatexPrinterM LatexData := do
  if kind.isAnonymous then
    failure
  for pp in latexPPAttribute.getValues (← getEnv) kind do
    try
      return ← pp e
    catch _ => pure ()
  if kind.getRoot != kind then
    latexPPFor e kind.getRoot
  else
    failure

/-- Runs the pretty printer for `e` using the `latexPPFor` algorithm with kind `getExprKind e`,
and if this fails it runs `defaultLatexPP`. -/
def latexPP (e : Expr) : LatexPrinterM LatexData :=
  latexPPFor e (getExprKind e) <|> defaultLatexPP e

/-- Run the LaTeX pretty printer for the expression `e`, using the given configuration. -/
def run_latexPP (e : Expr) (config : Config) : MetaM String := do
  let pp : LatexPrinterM LatexData := latexPP e
  let data : LatexData ← (pp.run config).run' {}
  return data.latex.1

/-- Pretty prints an expression that is a function application using the printers tagged with the
`latex_pp_app` attribute for the specified kind. If they fail, tries using `kind.getRoot` and
then `any`. -/
partial def latexPPAppFor (kind : Name) (f : Expr) (args : Array Expr) (pkinds : Array ParamKind) : LatexPrinterM LatexData := do
  if kind.isAnonymous then
    failure
  for pp in latexPPAppAttribute.getValues (← getEnv) kind do
    try
      return ← pp f args pkinds
    catch _ => pure ()
  if kind.getRoot != kind then
    latexPPAppFor kind.getRoot f args pkinds
  else if kind != `any then
    latexPPAppFor `any f args pkinds
  else
    failure

end LeanTeX
