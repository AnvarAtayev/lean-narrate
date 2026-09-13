import Narrate.English
import Narrate.Render

/-!
# The linter

Lean runs every registered linter after each command, and a linter, unlike a command
elaborator, can read that command's info trees, where both the statement and every
tactic step are recorded. That is what lets `import Narrate` narrate a file with no
other changes.
-/

open Lean Elab Command Linter

register_option linter.narrate : Bool := {
  defValue := true
  descr := "narrate each theorem and its proof in English in the Infoview"
}

namespace Narrate

/-- The goal of the outermost tactic block. -/
def rootGoal (t : InfoTree) : Option (ContextInfo × MVarId) :=
  let best := t.foldInfo (init := none) fun ci info best =>
    match info, info.stx.getRange? with
    | .ofTacticInfo { goalsBefore := [g], .. }, some r =>
      let w := r.stop.byteIdx - r.start.byteIdx
      match best with
      | some (w', _, _) => if w > w' then some (w, ci, g) else best
      | none => some (w, ci, g)
    | _, _ => best
  best.map fun (_, ci, g) => (ci, g)

/-- What a command claims. A named declaration is looked up in the environment; an
`example` has no name, so its claim is rebuilt from the root goal. -/
def claimOf (trees : Array InfoTree) : CommandElabM (Option Claim) := do
  let env ← getEnv
  let mut named := false
  for t in trees do
    for declName in getDeclsByBody t do
      let some info := env.find? declName | continue
      named := true
      if ← liftTermElabM (Meta.isProp info.type) then
        return some (toString declName, ← liftTermElabM (english info.type))
  if named then return none
  for t in trees do
    if let some (ci, g) := rootGoal t then
      return some ("example", ← ci.runMetaM {} (statementEnglish g))
  return none

def narrateLinter : Linter where
  run := withSetOptionIn fun _ => do
    unless getLinterValue linter.narrate (← getLinterOptions) do return
    -- Only files that import `Narrate` themselves, not everything downstream of them.
    unless (← getEnv).imports.any (·.module == `Narrate) do return
    if (← get).messages.hasErrors then return
    let trees := (← getInfoTrees).toArray
    let claim ← claimOf trees
    let steps ← proofSteps trees
    if claim.isNone && steps.isEmpty then return
    logInfo (← liftCoreM <| MessageData.ofHtml (narrationHtml claim steps)
      (narrationText claim steps))

initialize addLinter narrateLinter

end Narrate
