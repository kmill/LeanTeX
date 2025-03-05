import LeanTeX.Basic
import ProofWidgets.Component.HtmlDisplay

namespace LeanTeX

open Lean Elab Tactic ProofWidgets ProofWidgets.Jsx

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/--
Command for displaying an expression in LaTeX form.
-/
elab tk:"#texify " e:term : command => do
  Elab.Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTerm e none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let res ← run_latexPP e {}
    displayMarkdown s!"$\\displaystyle {res}$" tk

/--
Tactic for displaying the goal in LaTeX form.
-/
elab tk:"texify" : tactic => withMainContext do
  let mut lines : Array String := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      let var ← run_latexPP decl.toExpr {}
      let type ← run_latexPP (← instantiateMVars decl.type) {}
      if let some value := decl.value? then
        let val ← run_latexPP (← instantiateMVars value) {}
        lines := lines.push s!"{var} : {type} := {val}"
      else
        lines := lines.push s!"{var} : {type}"
  let goal ← run_latexPP (← instantiateMVars (← getMainTarget)).consumeMData {}
  lines := lines.push s!"\\vdash {goal}"
  let md := String.intercalate "\n\n" (lines
    |>.map (fun line => s!"$\\displaystyle {line}$")
    |>.toList)
  displayMarkdown md tk
