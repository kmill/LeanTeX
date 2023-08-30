import Lean.Data
import Lean.KeyedDeclsAttribute
import Lean.PrettyPrinter
import Std.Lean.Parser
import Lean.Elab.Command
import Lean.Elab.AuxDef

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

/-- Configuration for the `LatexPrinterM` monad. -/
structure Config where
  /-- Represents how nested of a subexpression we are looking at.
   This lets pretty printers decide to use more compact representations.
   It's only heuristic, where the number should be larger in proportion to how small the expression will be.-/
  smallness : Nat := 0
  /-- Whether implication is right associative -/
  implicationAssoc : Bool := false
  /-- Whether to omit binders in pi/forall -/
  omitBinders : Bool := false
  /-- Whether to use subscripts for arguments to families of types/sets -/
  familySubscripts : Bool := true
  /-- Represents whether the expression is for inline or display style output. (Not used yet) -/
  displayStyle : Bool := true
  /-- Whether to insert mathjax tooltips -/
  mathjaxTooltips : Bool := false
  /-- List of names to avoid when processing binders. Binders come with a default name, but we want
  to avoid name shadowing with things in the local context. -/
  avoidNames : List Name := []
  /-- Whether to allow binders to shadow names in the local context, provided that the local variables
  they shadow do not appear within the body of the forall/lambda. -/
  allowShadowing : Bool := true

structure State where

deriving Inhabited

/-- Monad for the entire LaTeX math expression pretty printer. Extends `MetaM` with some
configuration and a (currently unused) state. -/
abbrev LatexPrinterM := ReaderT Config (StateRefT State MetaM)

/-- Run the pretty printer in a context that has more limited space available.
For example, the pretty printer for division runs its numerator and denominator pretty
printers with extra smallness. -/
def withExtraSmallness (sm_inc : Nat) (m : LatexPrinterM α) : LatexPrinterM α :=
  ReaderT.adapt (λ state => { state with smallness := state.smallness + sm_inc }) m

/-- Run the pretty printer in a context that avoids using all the names in `extraNames` when
processing binders. Concretely, `m` is executed with `extraNames` appended to `avoidNames`. -/
def withAvoidNames (extraNames : List Name) (m : LatexPrinterM α) : LatexPrinterM α :=
  ReaderT.adapt (λ state => { state with avoidNames := extraNames ++ state.avoidNames }) m

/-- Builds a string with given tooltip if the current configuration allows tooltip,
returns the original string otherwise. -/
def maybeWithTooltip (s tooltip : String) : LatexPrinterM String := do
  let b := (← read).mathjaxTooltips
  if b then
    return s!"\\texttip\{{s}}\{{tooltip}}"
  else
    return s

/-- Binding powers. We attach these to left and right sides of an expression in
a `LatexData.Row` expression. -/
inductive BP
  /-- never parenthesize -/
  | Infinity
  /-- parenthesize when outer binding power is ≥ bp -/
  | NonAssoc (bp : Nat) 
  /-- parenthesize when outer binding power is > bp -/
  | Assoc (bp : Nat) 
deriving Inhabited

/-- Given two binding power descriptions for a particular direction, merge them into
one that's the weaker of the two. -/
def BP.merge : BP → BP → BP
| Infinity, bp2 => bp2
| bp1, Infinity => bp1
| NonAssoc bp1, NonAssoc bp2 => NonAssoc (min bp1 bp2)
| NonAssoc bp1, Assoc bp2 => if bp2 < bp1 then Assoc bp2 else NonAssoc bp1
| Assoc bp1, NonAssoc bp2 => if bp1 < bp2 then Assoc bp1 else NonAssoc bp2
| Assoc bp1, Assoc bp2 => Assoc (min bp1 bp2)

/-- Given an outer binding power, is the given `BP` "safe"? That is, can it avoid using parentheses? -/
def BP.isSafe : (bp : BP) → (outer : Nat) → Bool
  | Infinity, _ => true
  | NonAssoc bp, bp' => bp' < bp
  | Assoc bp, bp' => bp' ≤ bp

/-- Intermediate representation for LaTeX data.

* `Atom` is for anything that can support superscripts and subscripts without needing parentheses.
* `Row` is for anything that is a row of operators and operands.
  Some constructs (like fractions) use this so that superscripts/subscripts add parentheses.

The `bigness` value represents whether this is a "big" expression.
It helps decide whether to use `( ... )` or `\left( ... \right)`.

-/
inductive LatexData where
  /-- anything that can support superscripts and subscripts without needing parentheses -/
  | Atom (latex : String) (bigness : Nat := 0) (sup? : Option LatexData) (sub? : Option LatexData)
  /-- anything that is a row of operators and operands -/
  | Row (latex : String) (lbp : BP) (rbp : BP) (bigness : Nat)
deriving Inhabited

/-- The effective left binding power. For a `LatexData.Atom`, this is infinity. -/
def LatexData.lbp : LatexData → BP
| Atom .. => BP.Infinity
| Row _ lbp _ _ => lbp

/-- The effective right binding power. For a `LatexData.Atom`, this is infinity. -/
def LatexData.rbp : LatexData → BP
| Atom .. => BP.Infinity
| Row _ _ rbp _ => rbp

/-- Return a string representation of a `LatexData` along with its bigness.
For example, with a `LatexData.Atom`, this is the algorithm that finally encodes
the superscript and subscript expressions as LaTeX. -/
def LatexData.latex : LatexData → String × Nat
| Atom latex bigness sup? sub? =>
  let (latex, bigness) :=
    if let some sup := sup? then
      let (s, b) := sup.latex
      (s!"{latex}^\{{s}}", bigness + b)
    else (latex, bigness)
  let (latex, bigness) :=
    if let some sub := sub? then
      let (s, b) := sub.latex
      (s!"{latex}_\{{s}}", bigness + b)
    else (latex, bigness)
  (latex, bigness)
| Row latex _lbp _rbp bigness => (latex, bigness)

/-- Attach a string tooltip to some `LatexData` if the configuration allows it,
returns the original data otherwise. -/
def LatexData.maybeWithTooltip : LatexData → String → LatexPrinterM LatexData
  | Atom latex bigness sup? sub?, tooltip => do return Atom (← LeanTeX.maybeWithTooltip latex tooltip) bigness sup? sub?
  | Row latex lbp rbp bigness, tooltip => do return Row (← LeanTeX.maybeWithTooltip latex tooltip) lbp rbp bigness

/-- Put parentheses around a string, using positivity of the `bigness` value to determine 
whether or not to use `\left` and `\right` to get appropriate sizing. (Note that we do this
conditionally because the resizable parentheses tend not to render correctly as
normal-sized parentheses.) -/
def wrapParens (s : String) (bigness : Nat) : String :=
  if bigness > 0 then
    s!"\\left({s}\\right)"
  else
    s!"({s})"

/-- Just like `wrapParens` but for square brackets (`[` and `]`). -/
def wrapBrackets (s : String) (bigness : Nat) : String :=
  if bigness > 0 then
    s!"\\left\\lbrack\{}{s}\\right\\rbrack\{}"
  else
    s!"\\lbrack\{}{s}\\rbrack\{}"

/-- Ensure the latex data is an `Atom`, wrapping in parentheses if necessary. -/
def LatexData.toAtom : LatexData → LatexData
| d@(Atom ..) => d
| Row latex _lbp _rbp bigness => Atom (wrapParens latex bigness) bigness none none

/-- Ensure the latex data is a `Row`. If it was an `Atom`, we set the binding powers to infinity. -/
def LatexData.toRow : LatexData → LatexData
| d@(Atom ..) =>
  let (latex, bigness) := d.latex
  Row latex .Infinity .Infinity bigness
| d@(Row ..) => d

/-- Wrap the latex data in parentheses and make it an `Atom`.
(This is different from `LatexData.toAtom` because this one *always* wraps in parentheses.)
Optionally attach superscripts and subscripts at the same time. -/
def LatexData.parens (data : LatexData) (sup? sub? : Option LatexData := none) : LatexData :=
  let (latex, bigness) := data.latex
  Atom (wrapParens latex bigness) bigness sup? sub?

/-- Just like `LatexData.parens` but for square brackets. -/
def LatexData.brackets (data : LatexData) (sup? sub? : Option LatexData := none) : LatexData :=
  let (latex, bigness) := data.latex
  Atom (wrapBrackets latex bigness) bigness sup? sub?

/-- Attach a superscript, adding parentheses if necessary. In particular the result
will always be an `Atom`. -/
def LatexData.sup (d s : LatexData) : LatexData :=
  match d with
  | Atom latex bigness none sub? => Atom latex bigness (some s) sub?
  | _ => d.parens s none

/-- Attach a subscript, adding parentheses if necessary. In particular the result
will always be an `Atom`. -/
def LatexData.sub (d s : LatexData) : LatexData :=
  match d with
  | Atom latex bigness sup? none => Atom latex bigness sup? s
  | _ => d.parens none s

/-- Add parentheses if needed given that there is something with binding
power `bp` on the left. -/
def LatexData.protectLeft (d : LatexData) (bp : Nat) : LatexData :=
  if d.lbp.isSafe bp then d else d.parens

/-- Add parentheses if needed given that there is something with binding
power `bp` on the right. -/
def LatexData.protectRight (d : LatexData) (bp : Nat) : LatexData :=
  if d.rbp.isSafe bp then d else d.parens

/-- Add parentheses if needed given that there is something with binding
power `bp` on both the left and right. -/
def LatexData.protect (d : LatexData) (bp : Nat) : LatexData :=
  if d.lbp.isSafe bp ∧ d.rbp.isSafe bp then d else d.parens

/-- Convert to a `Row` and update the binding powers using `BP.merge`.
Does not wrap in parentheses. -/
def LatexData.mergeBP (d : LatexData) (lbp rbp : BP := .Infinity) : LatexData :=
  let (latex, bigness) := d.latex
  Row latex (d.lbp.merge lbp) (d.rbp.merge rbp) bigness

/-- Override the existing binding powers (and convert to a `Row` if needed). -/
def LatexData.resetBP (d : LatexData) (lbp : BP := d.lbp) (rbp : BP := d.rbp) : LatexData :=
  let (latex, bigness) := d.latex
  Row latex lbp rbp bigness

/-- Increment the `bigness` of the expression. -/
def LatexData.bigger (d : LatexData) (extra_bigness : Nat := 1) : LatexData :=
  match d with
  | Atom latex bigness sup? sub? => Atom latex (bigness + extra_bigness) sup? sub?
  | Row latex lbp rbp bigness => Row latex lbp rbp (bigness + extra_bigness)

/-- A string as a `LatexData`, represented as a `Row` with given binding powers.
(Note that this means it will be parenthesized if it gets a superscript or subscript.) -/
def LatexData.ofString (s : String) (bigness := 0) (lbp rbp : BP := .Infinity) : LatexData :=
  Row s lbp rbp bigness

/-- A string as a `LatexData`, represented as an `Atom`.
(Note that this means it will *not* be parenthesized if it gets a superscript or a subscript.) -/
def LatexData.atomString (s : String) : LatexData := Atom s 0 none none

/-- Associativity types, to control `LatexData.binOp`.

The constructors' docstrings below show how `(a + b) + c` and `a + (b + c)` would print
with the given associativity. -/
inductive Associativity
  /-- `(a + b) + c` and `a + (b + c)` -/
  | none
  /-- `a + b + c` and `a + (b + c)` -/
  | left
  /-- `(a + b) + c` and `a + b + c` -/
  | right

/-- A `LatexData.Row` set up for a binary operator with a specified associativity. -/
def LatexData.binOp (s : String) (assoc : Associativity) (bp : Nat) (bigness : Nat := 0) : LatexData :=
  match assoc with
  | .none => Row s (.NonAssoc bp) (.NonAssoc bp) bigness
  | .left => Row s (.NonAssoc bp) (.Assoc bp) bigness
  | .right => Row s (.Assoc bp) (.NonAssoc bp) bigness

/-- A `LatexData.Row` set up for a nonassociative binary operator. -/
def LatexData.nonAssocOp (s : String) (bp : Nat) : LatexData := binOp s .none bp

/-- A `LatexData.Row` set up for a left-associative binary operator. -/
def LatexData.leftAssocOp (s : String) (bp : Nat) : LatexData := binOp s .left bp 

/-- A `LatexData.Row` set up for a right-associative binary operator. -/
def LatexData.rightAssocOp (s : String) (bp : Nat) : LatexData := binOp s .right bp

/-- Append two `LatexData` to create a `Row`. Merges left binding powers and right binding powers.

The reason for merging this way is that binding powers represent how resistant an expression
is to be broken up if it is inserted into another expression. "A chain is only as strong as its
weakest link" applies here. -/
instance : Append LatexData where
  append d1 d2 :=
    let (d1_latex, d1_bigness) := d1.latex
    let (d2_latex, d2_bigness) := d2.latex
    .Row (d1_latex ++ d2_latex) (d1.lbp.merge d2.lbp) (d1.rbp.merge d2.rbp) (max d1_bigness d2_bigness)

/-- Use `LatexData.ofString` to append a string. -/
instance : HAppend LatexData String LatexData where
  hAppend d s := d ++ LatexData.ofString s

/-- Use `LatexData.ofString` to append a string. -/
instance : HAppend String LatexData LatexData where
  hAppend s d := LatexData.ofString s ++ d

/-- Create a `\frac{..}{..}` as a `Row`, which ensures any added superscripts and
subscripts will introduce parentheses. See also `LatexData.tfrac`. -/
def LatexData.frac (a b : LatexData) : LatexData :=
  let (latexa, bignessa) := a.latex
  let (latexb, bignessb) := b.latex
  Row s!"\\frac\{{latexa}}\{{latexb}}" .Infinity .Infinity (max 1 (bignessa + bignessb))

/-- Create a `\tfrac{..}{..}` as a `Row`, which ensures any added superscripts and
subscripts will introduce parentheses. See also `LatexData.frac`. -/
def LatexData.tfrac (a b : LatexData) : LatexData :=
  let (latexa, bignessa) := a.latex
  let (latexb, bignessb) := b.latex
  Row s!"\\tfrac\{{latexa}}\{{latexb}}" .Infinity .Infinity (max 1 (bignessa + bignessb))

/-- Create intercalated `LatexData` producing a `LatexData.Row`.
The resulting binding powers are set to `Infinity`, so be sure to update them with, for
example, `LatexData.resetBP` if needed. -/
def LatexData.intercalate (sep : String) (items : Array LatexData) : LatexData :=
  let latex := items.map LatexData.latex
  let bigness := latex.foldl (λ m (_, b) => max m b) 0
  Row (sep.intercalate <| Array.toList <| latex.map Prod.fst) .Infinity .Infinity bigness

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

/-- User command for turning arbitrary expressions into a LaTeX form.

Use with `#guard_msgs` from std4 to create tests for the latex output.
It prints the output with normalized spaces. -/
elab tk:"#latex " e:term : command => do
  Elab.Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTerm e none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let res ← run_latexPP e {}
    -- Normalize the spaces by collapsing all strings of whitespace into a single space character.
    let res := " ".intercalate (res |>.split Char.isWhitespace |>.filter (not ·.isEmpty))
    logInfoAt tk res

namespace RuleSyntax
open Lean.Elab Lean.Elab.Command

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
    let name ← resolveGlobalConstNoOverloadWithInfo id
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
    match alts.back with
    | `(Parser.Term.matchAltExpr| | _ => $_)
    | `(Parser.Term.matchAltExpr| | $_:ident => $_) => return alts
    | _ => return alts.push <| ← `(Parser.Term.matchAltExpr| | _ => failure)

@[command_elab latex_pp_const_syntax] def elab_latex_pp_const_rule : CommandElab :=
  adaptExpander fun
  | `(command| $[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind?:attrKind
                latex_pp_const_rule $name:ident := $body:term $[$whereClause?:whereDecls]?) => do
    let c ← resolveGlobalConstNoOverloadWithInfo name
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
    match alts.back with
    | `(Parser.Term.matchAltExpr| | $x, $y => $_) =>
      if isCatchAllPatt x && isCatchAllPatt y then
        return alts
      else
        return alts.push fail
    | _ => return alts.push fail

end RuleSyntax

end LeanTeX
