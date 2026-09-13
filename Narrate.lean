import Narrate.Linter

/-!
# Narrate

Narrates Lean 4 proofs in English, in the Infoview. Importing this module is the
whole setup: every theorem and `example` in the importing file has its statement
restated in English and its tactic proof narrated step by step.

Disable it for a file with `set_option linter.narrate false`.
-/
