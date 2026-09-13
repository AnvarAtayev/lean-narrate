# Narrate

Narrate Lean 4 proofs in English, in the Infoview.

Add `import Narrate` and every theorem and `example` in that file has its
statement restated in English and its tactic proof narrated step by step.

```lean
import Narrate

theorem or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq
```

```
or_swap: for all propositions P Q, if P or Q then Q or P
1. We proceed using h
     [rcases h with hp | hq]  this splits into 2 cases: hp : P ⊢ Q ∨ P  /  hq : Q ⊢ Q ∨ P
Case 1: Assume hp : P
2. Let's prove that P
     [right]  it remains to show P
3. We conclude by hp
     [exact hp]  that closes this case
Case 2: Assume hq : Q
4. Let's prove that Q
     [left]  it remains to show Q
5. We conclude by hq
     [exact hq]  that closes the goal. ∎
```

Each step has two lines: a sentence, then the tactic as written and exactly how
the goal changed. Case splits, including `induction`, open each case with what
it assumes.

An ε-δ proof with Mathlib:

```lean
import Mathlib
import Narrate

theorem cont_linear (x₀ : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |2 * x - 2 * x₀| < ε := by
  intro ε hε
  use ε / 2
  constructor
  · positivity
  · intro x hx
    rw [← mul_sub, abs_mul, abs_two]
    linarith
```

```
cont_linear: for every x₀ : ℝ, for every ε > 0, there is some δ > 0 such that for every x : ℝ, if |x - x₀| < δ then |2 * x - 2 * x₀| < ε
1. Fix ε > 0
     [intro ε hε]  we now know ε : ℝ; hε : ε > 0, and it remains to show ∃ δ > 0, ∀ (x : ℝ), |x - x₀| < δ → |2 * x - 2 * x₀| < ε
2. Let's prove that ε / 2 works
     [use ε / 2]  it remains to show ε / 2 > 0 ∧ ∀ (x : ℝ), |x - x₀| < ε / 2 → |2 * x - 2 * x₀| < ε
3. We prove each part in turn
     [constructor]  this splits into 2 cases: ⊢ ε / 2 > 0  /  ⊢ ∀ (x : ℝ), |x - x₀| < ε / 2 → |2 * x - 2 * x₀| < ε
Case 1: Let's prove that ε / 2 > 0
4. We conclude by computation
     [positivity]  that closes this case
Case 2: Let's prove that ∀ (x : ℝ), |x - x₀| < ε / 2 → |2 * x - 2 * x₀| < ε
5. Fix x : ℝ, then Assume hx : |x - x₀| < ε / 2
     [intro x hx]  we now know x : ℝ; hx : |x - x₀| < ε / 2, and it remains to show |2 * x - 2 * x₀| < ε
6. We rewrite using ← mul_sub, abs_mul, abs_two, which becomes 2 * |x - x₀| < ε
     [rw [← mul_sub, abs_mul, abs_two]]  it remains to show 2 * |x - x₀| < ε
7. We conclude by computation
     [linarith]  that closes the goal. ∎
```

## Installation

In `lakefile.toml`:

```toml
[[require]]
name = "narrate"
git = "https://github.com/AnvarAtayev/lean-narrate"
rev = "v4.34.0-rc2"
```

or in `lakefile.lean`:

```lean
require narrate from git "https://github.com/AnvarAtayev/lean-narrate" @ "v4.34.0-rc2"
```

Then run `lake update narrate` and add `import Narrate` to a file.

Releases are tagged with the Lean version they support, the same scheme Mathlib
uses: set `rev` to the tag matching your `lean-toolchain`. The only release so
far is `v4.34.0-rc2`. If you also use Mathlib, list Mathlib's `require` first so
its ProofWidgets version is used.

## Usage

Importing `Narrate` switches narration on for that file only. Files that import
it indirectly are not narrated. To switch it off:

```lean
set_option linter.narrate false
```

[Examples/Demo.lean](Examples/Demo.lean) covers the main cases using core Lean:
run `lake env lean Examples/Demo.lean`.

## How it works

Narration is a linter. Lean runs linters after each command, and a linter can
read the command's info trees: the record of every tactic step with the goals
before and after it.

| Module | Role |
|---|---|
| `Narrate/Linter.lean` | Collect each declaration's info trees |
| `Narrate/English.lean` | Translate the statement into English |
| `Narrate/Steps.lean` | Pick out the proof steps and diff their goals |
| `Narrate/Phrasebook.lean` | Word each step, in the style of Verbose Lean 4 |
| `Narrate/Render.lean` | Show HTML in the Infoview, text in a terminal |

A tactic without a phrasebook entry reads "We apply …". To add one, extend
`verboseFor` in `Narrate/Phrasebook.lean`.

## Limitations

- Automation (`simp`, `omega`, `linarith`, …) reads "We conclude by
  computation". Only the goal diff shows what it did.
- `rw [foo]` names `foo` but not what it states.
- Term-mode proofs show their statement only.
- Narration is logged as info messages, so `lake build` prints it too.
- The sentence is heuristic. The goal diff underneath is exact.

## Related work

- [Verbose Lean 4](https://github.com/PatrickMassot/verbose-lean4) goes the other
  way: you write controlled English and Lean checks it. Narrate borrows its
  wording. No code is shared.
- [Paperproof](https://github.com/Paper-Proof/paperproof) reads the same info
  trees and draws the proof as a tree in a VS Code panel.
- Mathlib's `#explode` shows a proof term as a Fitch-style table.

## Citing

If you use Narrate in your work, please cite it. GitHub's "Cite this repository"
button reads [CITATION.cff](CITATION.cff), or use:

```bibtex
@software{atayev_narrate_2026,
  author = {Atayev, Anvar},
  title  = {Narrate: English narration of Lean 4 proofs},
  year   = {2026},
  url    = {https://github.com/AnvarAtayev/lean-narrate}
}
```

## License

Apache-2.0. See [LICENCE](LICENCE).
