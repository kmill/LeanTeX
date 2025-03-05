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
  -- State for variable merging.
  -- Example, to write `x, y : ℝ` rather than `x : ℝ` and `y : ℝ` independently
  let mut currCDecl? : Option (Array String × String) := none
  let flush (lines : Array String) (currCDecl? : Option (Array String × String)) :
      Array String × Option (Array String × String) :=
    if let some (vars, type) := currCDecl? then
      (lines.push s!"{String.intercalate ", " vars.toList} : {type}", none)
    else
      (lines, none)
  let pushCDecl (lines : Array String) (currCDecl? : Option (Array String × String))
      (var : String) (type : String) :
      Array String × Option (Array String × String) := Id.run do
    if let some (vars, type') := currCDecl? then
      if type == type' then
        return (lines, (vars.push var, type'))
    let (lines, _) := flush lines currCDecl?
    return (lines, some (#[var], type))
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      let var ← run_latexPP decl.toExpr {}
      let type ← run_latexPP (← instantiateMVars decl.type) {}
      if let some value := decl.value? then
        (lines, currCDecl?) := flush lines currCDecl?
        let val ← run_latexPP (← instantiateMVars value) {}
        lines := lines.push s!"{var} : {type} := {val}"
      else
        (lines, currCDecl?) := pushCDecl lines currCDecl? var type
  (lines, _) := flush lines currCDecl?
  let goal ← run_latexPP (← instantiateMVars (← getMainTarget)).consumeMData {}
  lines := lines.push s!"\\vdash {goal}"
  let md := String.intercalate "\n\n" (lines
    |>.map (fun line => s!"$\\displaystyle {line}$")
    |>.toList)
  displayMarkdown md tk
