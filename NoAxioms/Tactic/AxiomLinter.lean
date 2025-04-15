import Lean.Util.CollectAxioms
import Lean.Linter

open Lean Elab

namespace NoAxioms

register_option linter.noAxioms : Bool :=
  {
    defValue := true
    descr := "show a warning if a declaration depends on any axioms"
  }

def noAxiomsLinter : Linter where
  run := withSetOptionIn <| fun stx => do
    unless (← getBoolOption linter.noAxioms.name true) do
      return
    for tree in (← getInfoTrees) do
      if tree matches .context .. then
        discard <| tree.collectTermInfoM fun ci ti => do
          unless ti.isBinder do
            return none
          let e := ti.expr
          unless e.isConst do
            return none
          let axioms ← ci.runCoreM (collectAxioms e.constName!)
          unless axioms.isEmpty do
            Linter.logLint linter.noAxioms ti.stx m!"declaration uses axioms"
          return (none : Option Unit)

initialize
  addLinter noAxiomsLinter

end NoAxioms
