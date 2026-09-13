import Narrate

/-!
# Demo

Ordinary Lean; `import Narrate` is the only addition. Put the cursor on a declaration
and read the Infoview, or run `lake env lean Examples/Demo.lean`.
-/

theorem le_succ' (n : Nat) : n ≤ n + 1 := by omega

theorem modus_ponens (P Q : Prop) : P → (P → Q) → Q := by
  intro hp hpq
  exact hpq hp

example : ∃ n : Nat, 5 * n = 35 := by exists 7

-- A term-mode proof has no steps, so only its claim is shown.
theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

-- Each bullet's steps are narrated.
theorem or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

-- Each branch of the induction is narrated.
theorem double_eq (n : Nat) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [double, ih]
    omega

-- The `by omega` belongs to `key`, so it is not narrated as a step.
theorem side_proof (a b : Nat) : a + b - b = a := by
  have key : a + b - b = a := by omega
  exact key
