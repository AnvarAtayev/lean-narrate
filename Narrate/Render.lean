import Narrate.Steps
import ProofWidgets.Component.HtmlDisplay

/-!
# Rendering

A narration is shown as HTML in the Infoview, with a plain-text version for the
terminal (and as the widget's fallback).
-/

open Lean ProofWidgets

namespace Narrate

/-- What a declaration claims: its name (or `example`) and the claim in English. -/
abbrev Claim := String × String

def stepHtml (i : Nat) (s : Step) : Html :=
  let header : Array Html := match s.header with
    | none => #[]
    | some h => #[.element "div" #[("style", json% {fontStyle: "italic"})] #[.text h]]
  .element "div" #[("style", json% {marginBottom: "0.7em"})] <| header ++ #[
    .element "div" #[] #[
      .element "span" #[("style", json% {opacity: "0.45"})] #[.text s!"{i}. "],
      .element "span" #[("style", json% {fontWeight: "600"})] #[.text s.verbose]
    ],
    .element "div" #[("style", json% {marginLeft: "1.6em", opacity: "0.7"})] #[
      .element "code" #[] #[.text s.tactic],
      .text s!"  -  {s.outcome}"
    ]
  ]

def narrationHtml (claim : Option Claim) (steps : Array Step) : Html :=
  let header : Array Html := match claim with
    | none => #[]
    | some (label, text) =>
      #[.element "div" #[("style", json% {marginBottom: "0.6em"})]
        #[.element "b" #[] #[.text s!"{label}: "], .text text]]
  .element "div" #[("style", json% {lineHeight: "1.45"})]
    (header ++ steps.zipIdx.map fun (s, i) => stepHtml (i + 1) s)

def narrationText (claim : Option Claim) (steps : Array Step) : String :=
  let header := match claim with
    | none => []
    | some (label, text) => [s!"{label}: {text}"]
  let lines := steps.zipIdx.toList.map fun (s, i) =>
    let header := match s.header with
      | none => ""
      | some h => h ++ "\n"
    s!"{header}{i + 1}. {s.verbose}\n     [{s.tactic}]  {s.outcome}"
  String.intercalate "\n" (header ++ lines)

end Narrate
