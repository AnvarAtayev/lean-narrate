import Lean

/-!
# English statements

Renders a proposition as prose. `∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε` becomes
"for every ε > 0, there is some N such that for every n ≥ N, |a n - L| < ε".
-/

open Lean Meta

namespace Narrate

/-- Relations that read as a bound on a variable, as in `∀ ε > 0`. -/
def boundHeads : List Name :=
  [``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``Ne, ``Membership.mem, ``Dvd.dvd]

/-- Is `cond` a bound on `x`, like `ε > 0` or `n ≥ N`? Checking the relation
matters: otherwise `P ∧ Q → R` would read as "for every P ∧ Q". -/
def isBoundOn (cond x : Expr) : Bool :=
  match cond.getAppFn with
  | .const n _ => boundHeads.contains n && cond.getAppArgs.any (· == x)
  | _ => false

/-- Does this statement have a shape the translator can take apart? -/
def isStructural (e : Expr) : Bool :=
  e.isForall || e.and?.isSome || (e.app2? ``Or).isSome
    || (e.app2? ``Exists).isSome || e.not?.isSome || e.iff?.isSome

/-- Deep beta reduction, so `(fun n => n + 3) a` reads as `a + 3`. -/
def deepBeta (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => return .done x.headBeta)

/-- `A → B → C` ↦ `(#[A, B], C)`. -/
partial def collectImps (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr × Expr) := do
  match e with
  | .forallE _ t b _ =>
    if (← isProp t) && !b.hasLooseBVars then collectImps b (acc.push t)
    else return (acc, e)
  | _ => return (acc, e)

/-- "for every n : ℕ," or "for all a b : ℕ," for one run of same-typed binders. -/
def binderPhrase (names : Array Name) (t : Expr) : MetaM String := do
  let ns := String.intercalate " " (names.toList.map toString)
  if t.isProp then
    return if names.size == 1 then s!"for every proposition {ns}," else s!"for all propositions {ns},"
  let tyStr := toString (← ppExpr t)
  return if names.size == 1 then s!"for every {ns} : {tyStr}," else s!"for all {ns} : {tyStr},"

/-- Group consecutive binders of the same type into one phrase. -/
def groupPhrase (xs : Array Expr) : MetaM String := do
  let mut out : Array String := #[]
  let mut names : Array Name := #[]
  let mut curTy : Option Expr := none
  for x in xs do
    let ty ← inferType x
    let nm ← x.fvarId!.getUserName
    match curTy with
    | none => curTy := some ty; names := #[nm]
    | some t =>
      if t == ty then names := names.push nm
      else
        out := out.push (← binderPhrase names t)
        curTy := some ty
        names := #[nm]
  if let some t := curTy then out := out.push (← binderPhrase names t)
  return String.intercalate " " out.toList

/-- Render a proposition as prose.

`nested` is `true` inside a larger statement, where an implication reads better as
"P implies Q" than "if P then Q".

Definitions are unfolded exactly one step, and only when that reveals structure:
enough to expand a user's `ConvergesTo` or Mathlib's `Even` and `Injective`, while
`Nat.Prime p` stays named instead of exploding into its internals. -/
partial def english (e : Expr) (nested : Bool := false) : MetaM String := do
  let e ← deepBeta (← instantiateMVars e)
  if let some (p, q) := e.and? then return s!"{← english p true} and {← english q true}"
  if let some (p, q) := e.app2? ``Or then return s!"{← english p true} or {← english q true}"
  if let some (p, q) := e.iff? then return s!"{← english p true} exactly when {← english q true}"
  if let some p := e.not? then return s!"it is not the case that {← english p true}"
  if let some (t, lam) := e.app2? ``Exists then
    match lam with
    | .lam n _ body _ =>
      return ← withLocalDeclD n t fun x => do
        let body := body.instantiate1 x
        -- `∃ δ, δ > 0 ∧ P` reads "there is some δ > 0 such that P"
        if let some (cond, rest) := body.and? then
          if isBoundOn cond x then
            return s!"there is some {← ppExpr cond} such that {← english rest true}"
        return s!"there is some {n} such that {← english body true}"
    | _ => return toString (← ppExpr e)
  match e with
  | .forallE _ t b _ =>
    if (← isProp t) && !b.hasLooseBVars then
      let (hyps, concl) ← collectImps e
      let hypStr := String.intercalate " and " (← hyps.mapM fun h => english h true).toList
      let cTxt ← english concl
      return if nested then s!"{hypStr} implies {cTxt}" else s!"if {hypStr} then {cTxt}"
    forallTelescope e fun xs body => do
      let mut i := 0
      for x in xs do
        if ← isProp (← inferType x) then break
        i := i + 1
      if i == 0 then return toString (← ppExpr e)
      let dataVars := xs.extract 0 i
      let rest ← mkForallFVars (xs.extract i xs.size) body
      -- `∀ ε, ε > 0 → P` reads "for every ε > 0, P"
      if let .forallE _ cond rest' _ := rest then
        if (← isProp cond) && !rest'.hasLooseBVars && isBoundOn cond dataVars.back! then
          let pre ← groupPhrase dataVars.pop
          let lead := if pre.isEmpty then "" else pre ++ " "
          return s!"{lead}for every {← ppExpr cond}, {← english rest'}"
      return s!"{← groupPhrase dataVars} {← english rest}"
  | _ =>
    if e.getAppFn.isConst then
      if let some e' ← unfoldDefinition? e then
        if isStructural e' then return ← english e' nested
    return toString (← ppExpr e)

/-- The full claim behind a goal, re-quantified over its local context, so an
anonymous `example` still reads as a standalone statement. -/
def statementEnglish (g : MVarId) : MetaM String :=
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let mut xs : Array Expr := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do xs := xs.push (.fvar d.fvarId)
    english (← mkForallFVars xs ty)

end Narrate
