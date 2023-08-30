import Lean

namespace LeanTeX

open Lean

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
