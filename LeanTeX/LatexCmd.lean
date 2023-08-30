import LeanTeX.Basic

namespace LeanTeX

open Lean

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