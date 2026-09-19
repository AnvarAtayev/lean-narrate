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

/-- The operand written first in `cond`, for the relations in `boundHeads`: `ε` in
`ε > 0`, `n` in `n ∈ A`. Membership takes the collection before the element; the
others take their operands in the order they are written. -/
def leftOperand (cond : Expr) : Option Expr :=
  match cond.getAppFn with
  | .const n _ =>
    let args := cond.getAppArgs
    if !boundHeads.contains n || args.size < 2 then none
    else if n == ``Membership.mem then args[args.size - 1]?
    else args[args.size - 2]?
  | _ => none

/-- Is `cond` a bound on `x`, like `ε > 0` or `n ≥ N`? Checking the relation matters:
otherwise `P ∧ Q → R` would read as "for every P ∧ Q". So does checking the side `x`
is on: `0 < n` is a hypothesis about `n`, which reads "if 0 < n then …", whereas the
bound `n > 0` reads "for every n > 0". -/
def isBoundOn (cond x : Expr) : Bool := leftOperand cond == some x

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

/-! ## Binding strength

A part of a statement is parenthesized when it binds more loosely than the place it
sits in, so that `(P ∨ Q) ∧ R` reads "(P or Q) and R" rather than "P or Q and R",
which English would read the other way round. Tightest first: an atom, a negation, a
conjunction or disjunction, an implication, a quantifier (which runs to the end). -/

def atomPrec : Nat := 5
def notPrec : Nat := 4
def andOrPrec : Nat := 3
def impPrec : Nat := 1
def quantPrec : Nat := 0

/-- `A ∧ B ∧ C` ↦ `#[A, B, C]`, so a chain reads as one list rather than nesting. -/
partial def flatten (parts : Expr → Option (Expr × Expr)) (e : Expr) : Array Expr :=
  match parts e with
  | some (p, q) => flatten parts p ++ flatten parts q
  | none => #[e]

/-- Render a proposition as prose.

`nested` is `true` inside a larger statement, where an implication reads better as
"P implies Q" than "if P then Q". `prec` is how tightly the place it sits in binds;
a statement that binds more loosely than that is parenthesized.

Definitions are unfolded exactly one step, and only when that reveals structure:
enough to expand a user's `ConvergesTo` or Mathlib's `Even` and `Injective`, while
`Nat.Prime p` stays named instead of exploding into its internals. -/
partial def english (e : Expr) (nested : Bool := false) (prec : Nat := quantPrec) :
    MetaM String := do
  let e ← deepBeta (← instantiateMVars e)
  let wrap (p : Nat) (s : String) : String := if p < prec then s!"({s})" else s
  if e.and?.isSome then
    let parts ← (flatten Expr.and? e).mapM (english · true atomPrec)
    return wrap andOrPrec (String.intercalate " and " parts.toList)
  if (e.app2? ``Or).isSome then
    let parts ← (flatten (·.app2? ``Or) e).mapM (english · true atomPrec)
    return wrap andOrPrec (String.intercalate " or " parts.toList)
  if let some (p, q) := e.iff? then
    -- Binds tighter than an implication, so `(P → Q) ↔ R` keeps its parentheses.
    return wrap impPrec s!"{← english p true (impPrec + 1)} exactly when \
      {← english q true (impPrec + 1)}"
  if let some p := e.not? then
    return wrap notPrec s!"it is not the case that {← english p true atomPrec}"
  if let some (t, lam) := e.app2? ``Exists then
    match lam with
    | .lam n _ body _ =>
      return ← withLocalDeclD n t fun x => do
        let body := body.instantiate1 x
        -- `∃ δ, δ > 0 ∧ P` reads "there is some δ > 0 such that P"
        if let some (cond, rest) := body.and? then
          if isBoundOn cond x then
            return wrap quantPrec s!"there is some {← ppExpr cond} such that \
              {← english rest true}"
        return wrap quantPrec s!"there is some {n} such that {← english body true}"
    | _ => return toString (← ppExpr e)
  match e with
  | .forallE _ t b _ =>
    if (← isProp t) && !b.hasLooseBVars then
      let (hyps, concl) ← collectImps e
      -- Several hypotheses are joined by "and", which would otherwise swallow the
      -- structure of each. A lone one is closed off by "then", so it only needs
      -- parentheses when it carries a "then" of its own, as `Injective f` does:
      -- "if (for all a b, if f a = f b then a = b) then …".
      let hypPrec := if nested || hyps.size > 1 then atomPrec else impPrec + 1
      let hypStr := String.intercalate " and " (← hyps.mapM (english · true hypPrec)).toList
      if nested then
        return wrap impPrec s!"{hypStr} implies {← english concl true atomPrec}"
      return wrap quantPrec s!"if {hypStr} then {← english concl}"
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
          return wrap quantPrec s!"{lead}for every {← ppExpr cond}, {← english rest'}"
      return wrap quantPrec s!"{← groupPhrase dataVars} {← english rest}"
  | _ =>
    if e.getAppFn.isConst then
      if let some e' ← unfoldDefinition? e then
        if isStructural e' then return ← english e' nested prec
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
