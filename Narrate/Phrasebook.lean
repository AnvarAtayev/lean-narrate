import Lean

/-!
# Phrasebook

Turns one tactic step into a sentence in the controlled English of Verbose Lean 4
(Patrick Massot): `Fix ε > 0`, `Assume h : P`, `By h applied to x using hx we get …`,
`Let's prove that N works`, `We conclude by …`.
-/

namespace Narrate

/-- A hypothesis, as the phrasebook sees it. -/
structure Hyp where
  name : String
  type : String
  /-- `true` for a proof `h : P`, `false` for data `x : ℝ`. -/
  isProp : Bool
  deriving Inhabited, BEq

/-- `String.trimAscii` returns a slice; this stays in `String`. -/
def trimS (s : String) : String := toString s.trimAscii

/-- The text after a tactic's leading token: `[key]` for `rw [key]`. -/
def afterHead (src head : String) : String :=
  if src.startsWith head then trimS (toString (src.drop head.length)) else src

def firstWord (s : String) : String := (s.splitOn " ").headD s

/-- Strip one layer of `[ ]` from a rewrite rule list. -/
def unbracket (s : String) : String :=
  let s := trimS s
  if s.startsWith "[" && s.endsWith "]" then trimS (toString ((s.drop 1).dropEnd 1)) else s

/-- Split off a tactic's location: `[h] at h'` ↦ `("[h]", some "h'")`, and
`[h]` ↦ `("[h]", none)`. -/
def splitLocation (s : String) : String × Option String :=
  match s.splitOn " at " with
  | [] | [_] => (trimS s, none)
  | before :: rest => (trimS before, some (trimS (String.intercalate " at " rest)))

/-- `h : P := proof` ↦ `h : P`. -/
def dropAssign (s : String) : String :=
  match s.splitOn ":=" with
  | [] => s
  | x :: _ => trimS x

/-- `⟨N, hN⟩ := ha ε hε` ↦ `ha ε hε`. -/
def assignedTerm (s : String) : String :=
  match s.splitOn ":=" with
  | _ :: rest@(_ :: _) => trimS (String.intercalate ":=" rest)
  | _ => s

/-- `ha ε hε` ↦ `ha applied to ε using hε`. An argument counts as a proof when the
local context says it is one; compound terms are left as written. -/
def appliedCtx (ctx : Array Hyp) (s : String) : String :=
  let t := trimS s
  if t.any (fun c => c == '⟨' || c == ',' || c == '(') then t
  else match t.splitOn " " with
    | [] => t
    | [only] => only
    | f :: args =>
      let isProof (a : String) : Bool := (ctx.find? fun h => h.name == a && h.isProp).isSome
      let vals := args.filter fun a => !isProof a
      let prfs := args.filter isProof
      let valPart := if vals.isEmpty then "" else s!" applied to {String.intercalate " " vals}"
      let prfPart := if prfs.isEmpty then "" else s!" using {String.intercalate " and " prfs}"
      s!"{f}{valPart}{prfPart}"

/-- `Fix x : ℝ, then Assume h : P` for hypotheses that just came into scope. -/
def introduceAll (hyps : Array Hyp) : String :=
  String.intercalate ", then " <| hyps.toList.map fun h =>
    if h.isProp then s!"Assume {h.name} : {h.type}" else s!"Fix {h.name} : {h.type}"

/-- The line opening case `i` (from 1) of a split made by `head`, like
`Case 2: Assume hq : Q` or `Induction step: Assume ih : …`. `gained` are the case's
new hypotheses and `goal` its target; the target is only restated when the split
changed it from `goalBefore`. -/
def caseHeader (head : String) (i : Nat) (gained : Array Hyp) (goal goalBefore : String) :
    String :=
  let label :=
    if head != "induction" then s!"Case {i}"
    else if gained.any (·.isProp) then "Induction step"
    else "Base case"
  let parts := (if gained.isEmpty then [] else [introduceAll gained])
    ++ (if goal != goalBefore then [s!"Let's prove that {goal}"] else [])
  if parts.isEmpty then label else s!"{label}: {String.intercalate ". " parts}"

/-- The sentence for one step.

* `head`, `src`: the tactic's leading token and source text
* `ctx`: hypotheses before the step; `gained`: hypotheses it added or changed
* `targetBefore`: the goal it was working on; `targetAfter`: what replaced that goal
* `closed`: whether it closed the goal it was working on, even if others remain
* `split`: whether it splits that goal into cases -/
def verboseFor (head src : String) (ctx gained : Array Hyp)
    (targetBefore targetAfter : String) (closed split : Bool) : String :=
  let args := afterHead src head
  let props := gained.filter (·.isProp)
  let objs := gained.filter (fun h => !h.isProp)
  let introduce := introduceAll gained
  match head with
  | "intro" =>
    match gained.toList with
    | [] => s!"Let's prove that {targetAfter}"
    -- `intro ε hε` with `hε : ε > 0` is Verbose Lean's bounded `Fix ε > 0`
    | [obj, prop] =>
      if !obj.isProp && prop.isProp && prop.type.startsWith (obj.name ++ " ") then
        s!"Fix {prop.type}"
      else introduce
    | _ => introduce
  | "obtain" | "rcases" | "cases" =>
    -- `obtain ⟨x, hx⟩ := h` and `rcases h with x | y` both name the term `h`
    let term := ((assignedTerm args).splitOn " with ").headD args
    let from_ := appliedCtx ctx term
    if split then
      s!"We proceed using {term}"
    -- `cases h` on an impossible hypothesis leaves nothing behind, and nothing to say
    -- beyond the fact it was used
    else if closed then s!"We conclude by {from_}"
    else
      let suchThat := String.intercalate " and " <|
        props.toList.map fun h => s!"({h.name} : {h.type})"
      let names := String.intercalate " " (objs.toList.map (·.name))
      match objs.isEmpty, props.isEmpty with
      | true, true => s!"We use {from_}"
      | true, false => s!"By {from_} we get {suchThat}"
      -- `obtain ⟨k, rfl⟩ := h` substitutes instead of naming a fact
      | false, true => s!"By {from_} we get {names}"
      | false, false => s!"By {from_} we get {names} such that {suchThat}"
  | "use" | "exists" => s!"Let's prove that {args} works"
  | "exact" => s!"We conclude by {appliedCtx ctx args}"
  | "apply" =>
    if closed then s!"We conclude by {appliedCtx ctx args}"
    else s!"By {appliedCtx ctx args} it suffices to prove that {targetAfter}"
  | "rw" | "rewrite" =>
    let (rules, loc) := splitLocation args
    let place := match loc with
      | none => ""
      | some "*" => " everywhere"
      | some l => s!" at {l}"
    if closed then s!"We rewrite using {unbracket rules}{place}, which closes the goal"
    else
      -- What the rewrite changed: the hypotheses rewritten at, and the goal if it was
      -- rewritten too. A single hypothesis is already named by `place`.
      let goalChanged := targetAfter != targetBefore
      let changes := match gained.toList, goalChanged with
        | [h], false => [h.type]
        | hyps, _ => hyps.map (fun h => s!"{h.name} : {h.type}")
            ++ (if goalChanged then [targetAfter] else [])
      if changes.isEmpty then s!"We rewrite using {unbracket rules}{place}"
      else s!"We rewrite using {unbracket rules}{place}, which becomes " ++
        String.intercalate "; " changes
  | "show" | "change" =>
    match splitLocation args with
    | (stmt, some loc) => s!"We reformulate {loc} as {stmt}"
    | (stmt, none) => s!"Let's prove that {stmt}"
  | "have" => s!"Fact {dropAssign args}"
  | "by_contra" =>
    match props.toList with
    | h :: _ => s!"Assume for contradiction {h.name} : {h.type}"
    | [] => "Assume for contradiction that the goal is false"
  | "left" | "right" => s!"Let's prove that {targetAfter}"
  | "constructor" =>
    if split then "We prove each part in turn"
    else if closed then "We conclude by the constructor"
    else s!"Let's prove that {targetAfter}"
  | "induction" => s!"We proceed by induction on {firstWord args}"
  | "ext" => s!"Fix {firstWord args}, and prove both sides agree"
  | "case" | "next" => if closed then "That case is done" else s!"Let's prove that {targetAfter}"
  | "unfold" => s!"We reformulate using the definition of {firstWord args}"
  | "subst" => s!"We substitute using {args}"
  | "push" => "We push the negation inwards"
  | "ring" | "ring_nf" | "norm_num" | "linarith" | "nlinarith" | "omega"
  | "positivity" | "decide" | "simp" | "simpa" | "field_simp" | "trivial" | "rfl" =>
    if closed then "We conclude by computation" else "We compute"
  | "sorry" => "This step is left unproved"
  | _ => if closed then s!"We conclude by {appliedCtx ctx src}" else s!"We apply {appliedCtx ctx src}"

end Narrate
