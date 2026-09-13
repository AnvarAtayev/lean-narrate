import Lean
import Narrate.Phrasebook

/-!
# Steps

Reads the steps of a tactic proof from Lean's info trees, and describes each one by
diffing the goal state before and after it. Because every sentence comes from states
Lean actually produced, the narration cannot describe something the proof did not do.
-/

open Lean Elab Meta Command

namespace Narrate

/-- One narrated proof step. -/
structure Step where
  /-- Opens the case this step starts, like `Case 2: Assume hq : Q`. -/
  header : Option String := none
  /-- The tactic as written, first line only. -/
  tactic : String
  /-- The step in Verbose-Lean-style English. -/
  verbose : String
  /-- What changed: new hypotheses, the remaining goal, splits and closures. -/
  outcome : String
  deriving Inhabited

/-! ## Goal snapshots -/

def hypInfos (g : MVarId) : MetaM (Array Hyp) :=
  g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        out := out.push
          -- An inaccessible name shows as `n✝`, as in the goal view.
          { name := if d.userName.hasMacroScopes then s!"{d.userName.eraseMacroScopes}✝"
                    else toString d.userName
            type := toString (← ppExpr d.type)
            isProp := ← isProp d.type }
    return out

def goalString (g : MVarId) : MetaM String :=
  g.withContext do return toString (← ppExpr (← g.getType))

/-- The leading token of a tactic: `rw` for `rw [foo]`. -/
def headOf (t : Syntax) : String :=
  let a := t[0].getAtomVal
  if a != "" then a
  else match t.getKind.components.getLast? with
    | some n => toString n
    | none => "?"

/-- The source text of a tactic: first line only, without trailing comments
(which `reprint` would otherwise keep). -/
def tacticSrc (stx : Syntax) : String :=
  let full := toString (stx.reprint.getD (toString stx)).trimAscii
  let full := match full.splitOn "--" with
    | x :: _ :: _ => trimS x
    | _ => full
  match full.splitOn "\n" with
  | [_] | [] => full
  | first :: _ => toString first.trimAscii ++ " …"

/-- A case as the outcome line shows it: `hp : P ⊢ Q ∨ P`. -/
def caseSummary (gained : Array Hyp) (goal : String) : String :=
  let hyps := String.intercalate ", " (gained.toList.map fun h => s!"{h.name} : {h.type}")
  if hyps.isEmpty then s!"⊢ {goal}" else s!"{hyps} ⊢ {goal}"

/-- Build a `Step` from the snapshots before and after a tactic. `cases` holds the new
hypotheses and target of each case the tactic splits into, and `last` marks the final
step of the proof, the only one that ends it. -/
def mkStep (head src : String) (ctx : Array Hyp) (targetBefore : String)
    (afterHyps : Array Hyp) (afterTargets : Array String) (nBefore : Nat)
    (cases : Array (Array Hyp × String)) (last : Bool) : Step :=
  let nAfter := afterTargets.size
  let split := !cases.isEmpty
  let closed := nAfter == 0 && !split
  let targetAfter := afterTargets[0]?.getD ""
  let gained := afterHyps.filter fun h => !ctx.contains h
  let outcome :=
    if split then
      let summaries := cases.toList.map fun (g, t) => caseSummary g t
      s!"this splits into {cases.size} cases: {String.intercalate "  /  " summaries}"
    else if closed then if last then "that closes the goal. ∎" else "that closes this case"
    else if nAfter < nBefore then s!"that case is done; {nAfter} goal(s) still open"
    else
      let gainedTxt := if gained.isEmpty then [] else
        [s!"we now know {String.intercalate "; " (gained.toList.map fun h => s!"{h.name} : {h.type}")}"]
      let targetTxt :=
        if targetAfter != targetBefore then [s!"it remains to show {targetAfter}"]
        else if gained.isEmpty then [s!"the goal is unchanged ({targetAfter})"]
        else []
      String.intercalate ", and " (gainedTxt ++ targetTxt)
  { tactic := src
    verbose := verboseFor head src ctx gained targetAfter closed split
    outcome }

/-! ## Reading steps from the info trees -/

/-- Info-tree nodes that are containers rather than proof steps. -/
def skipKinds : List Name :=
  [``Lean.Parser.Term.byTactic, ``Lean.Parser.Tactic.tacticSeq,
   ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed,
   `Lean.cdot, `Lean.cdotTk, `null]

/-- Tactics whose nested steps are real steps (the branches of a case split), rather
than a side proof belonging to the tactic itself. -/
def structuringHeads : List String :=
  ["induction", "cases", "case", "next", "focus", "all_goals", "any_goals",
   "first", "try", "repeat", "iterate", "rcases"]

def isOriginal (stx : Syntax) : Bool :=
  match stx.getHeadInfo with
  | .original .. => true
  | _ => false

/-- A candidate step: its source range, leading token, info-tree node, and the goals
it splits into, each with the metavariable context it lives in. -/
structure Cand where
  start : Nat
  stop : Nat
  head : String
  ci : ContextInfo
  ti : TacticInfo
  cases : Array (MetavarContext × MVarId)

/-- The goals the branches of `induction … with` or `cases … with` start from: the
topmost nodes below the tactic `ti` that work on a goal other than its own. -/
partial def branchGoals (ti : TacticInfo) : InfoTree → Array (MetavarContext × MVarId)
  | .context _ t => branchGoals ti t
  | .node info children =>
    match info with
    | .ofTacticInfo { goalsBefore := g :: _, mctxBefore, .. } =>
      if ti.goalsBefore.head? != some g then #[(mctxBefore, g)]
      else children.toArray.flatMap (branchGoals ti)
    | _ => children.toArray.flatMap (branchGoals ti)
  | .hole _ => #[]

/-- The goals a step splits into. Usually these are its new goals, but
`induction … with` closes its branches itself, leaving no goals behind, so for it
they are read from the branch nodes beneath it. -/
def casesOf (head : String) (ti : TacticInfo) (children : PersistentArray InfoTree) :
    Array (MetavarContext × MVarId) :=
  if ti.goalsAfter.length > ti.goalsBefore.length then
    let old := ti.goalsBefore.drop 1
    (ti.goalsAfter.filter (!old.contains ·)).toArray.map (ti.mctxAfter, ·)
  else if head == "induction" || head == "cases" then
    let branches := children.toArray.flatMap (branchGoals ti) |>.foldl (init := #[])
      fun acc (m, g) => if acc.any (·.2 == g) then acc else acc.push (m, g)
    if branches.size > 1 then branches else #[]
  else #[]

def candidates (t : InfoTree) : Array Cand :=
  t.foldInfoTree (init := #[]) fun ci node acc =>
    match node with
    | .node (.ofTacticInfo ti) children =>
      let isStep := match ti.stx with
        | .node _ k _ => !skipKinds.contains k
        | _ => false
      match ti.stx.getRange?, ti.stx.getPos? (canonicalOnly := true) with
      | some r, some _ =>
        if isStep then
          let head := headOf ti.stx
          acc.push { start := r.start.byteIdx, stop := r.stop.byteIdx, head, ci, ti
                     cases := casesOf head ti children }
        else acc
      | _, _ => acc
    | _ => acc

/-- Narrate one candidate. Goals are only meaningful in their own metavariable context,
hence `mctxBefore` and `mctxAfter`. Also returns the header for each case it opens. -/
def stepOfCand (c : Cand) (last : Bool) : CommandElabM (Step × Array (MVarId × String)) := do
  let ci := c.ci
  let ti := c.ti
  let (ctx, targetBefore) ← { ci with mctx := ti.mctxBefore }.runMetaM {} do
    match ti.goalsBefore with
    | [] => pure (#[], "")
    | g :: _ => return (← hypInfos g, ← goalString g)
  let (afterHyps, afterTargets) ← { ci with mctx := ti.mctxAfter }.runMetaM {} do
    match ti.goalsAfter with
    | [] => pure (#[], #[])
    | g :: rest => return (← hypInfos g, ← (g :: rest).toArray.mapM fun x => goalString x)
  let mut cases := #[]
  let mut headers := #[]
  for (mctx, g) in c.cases do
    let (hyps, goal) ← { ci with mctx }.runMetaM {} do return (← hypInfos g, ← goalString g)
    let gained := hyps.filter fun h => !ctx.contains h
    cases := cases.push (gained, goal)
    headers := headers.push (g, caseHeader c.head cases.size gained goal targetBefore)
  let step := mkStep c.head (tacticSrc ti.stx) ctx targetBefore afterHyps afterTargets
    ti.goalsBefore.length cases last
  return (step, headers)

/-- Every step of one declaration's proof, in source order.

The raw info trees are noisy, and two filters make them readable:

* **Macro expansions.** Where two nodes share a source position (`show` expands to
  `change`), the node from the original source wins.
* **Side proofs.** A step nested inside another step's source range belongs to that
  step: the `ring` in `have h : P := by ring` is not a step of the main proof. That
  inner `by` elaborates into its own info tree, which is why the rule is based on
  source ranges. Structuring tactics are exempt, so `induction` branches survive. -/
def proofSteps (trees : Array InfoTree) : CommandElabM (Array Step) := do
  let sorted := (trees.foldl (init := #[]) fun acc t => acc ++ candidates t).qsort
    fun a b => a.start < b.start
  let mut uniq : Array Cand := #[]
  let mut pending : Option Cand := none
  for c in sorted do
    match pending with
    | none => pending := some c
    | some cur =>
      if c.start == cur.start then
        if isOriginal c.ti.stx && !isOriginal cur.ti.stx then pending := some c
      else
        uniq := uniq.push cur
        pending := some c
  if let some cur := pending then uniq := uniq.push cur
  let swallowed (c : Cand) : Bool :=
    uniq.any fun o =>
      !structuringHeads.contains o.head
        && (o.start < c.start && c.stop ≤ o.stop || o.start ≤ c.start && c.stop < o.stop)
  let kept := uniq.filter (!swallowed ·)
  let mut steps : Array Step := #[]
  -- Headers of cases not yet entered, keyed by the case's goal.
  let mut unentered : Array (MVarId × String) := #[]
  for (c, i) in kept.zipIdx do
    let (step, headers) ← stepOfCand c (i + 1 == kept.size)
    let goal := c.ti.goalsBefore.head?
    let header := (unentered.find? fun (g, _) => some g == goal).map (·.2)
    unentered := unentered.filter fun (g, _) => some g != goal
    steps := steps.push { step with header }
    unentered := unentered ++ headers
  return steps

end Narrate
