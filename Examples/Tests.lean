import Narrate

/-!
# Tests

Each test pins the exact narration of a proof whose goal bookkeeping is easy to get
wrong: a step that closes one of several open goals, a rewrite aimed at a hypothesis,
a statement whose parts could be grouped more than one way. Run with
`lake env lean Examples/Tests.lean`; a test fails if the narration changes.

The narration of each theorem is also printed a second time, uncaptured, because the
linter narrates the `#guard_msgs` command as well as the theorem inside it.
-/

-- `#guard_msgs` captures every message the command produces, warnings included.
set_option linter.unusedVariables false

/-! ## A step is described by its own goal, never by one it did not touch -/

/--
info: apply_closes_one_of_two: for all propositions P Q, if P and Q then P and Q
1. We prove each part in turn
     [constructor]  this splits into 2 cases: ⊢ P  /  ⊢ Q
Case 1: Let's prove that P
2. We conclude by hp
     [apply hp]  that case is done; 1 goal(s) still open
Case 2: Let's prove that Q
3. We conclude by hq
     [exact hq]  that closes the goal. ∎
-/
#guard_msgs in
theorem apply_closes_one_of_two (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  apply hp
  exact hq

/--
info: rw_closes_one_of_two: for all a b : Nat, if a = b then a = b and 1 = 1
1. We prove each part in turn
     [constructor]  this splits into 2 cases: ⊢ a = b  /  ⊢ 1 = 1
Case 1: Let's prove that a = b
2. We rewrite using h, which closes the goal
     [rw [h]]  that case is done; 1 goal(s) still open
Case 2: Let's prove that 1 = 1
3. We conclude by computation
     [rfl]  that closes the goal. ∎
-/
#guard_msgs in
theorem rw_closes_one_of_two (a b : Nat) (h : a = b) : a = b ∧ 1 = 1 := by
  constructor
  rw [h]
  rfl

/-! ## A tactic aimed at a hypothesis is described by that hypothesis -/

/--
info: rw_at_hypothesis: for all a b : Nat, if a = b and a + 1 = 5 then True
1. We rewrite using h at h', which becomes b + 1 = 5
     [rw [h] at h']  we now know h' : b + 1 = 5
2. We conclude by computation
     [trivial]  that closes the goal. ∎
-/
#guard_msgs in
theorem rw_at_hypothesis (a b : Nat) (h : a = b) (h' : a + 1 = 5) : True := by
  rw [h] at h'
  trivial

/--
info: rw_everywhere: for all a b c : Nat, if a = b and a = c then b = c
1. We rewrite using h everywhere, which becomes h : b = b; h' : b = c
     [rw [h] at *]  we now know h : b = b; h' : b = c
2. We conclude by h'
     [exact h']  that closes the goal. ∎
-/
#guard_msgs in
theorem rw_everywhere (a b c : Nat) (h : a = b) (h' : a = c) : b = c := by
  rw [h] at *
  exact h'

/--
info: change_at_hypothesis: if 1 + 1 = 2 then True
1. We reformulate h as 2 = 2
     [change 2 = 2 at h]  we now know h : 2 = 2
2. We conclude by computation
     [trivial]  that closes the goal. ∎
-/
#guard_msgs in
theorem change_at_hypothesis (h : 1 + 1 = 2) : True := by
  change 2 = 2 at h
  trivial

/-! ## A step that produces no new fact still reads as a sentence -/

/--
info: obtain_substituting: for every n : Nat, if (there is some k such that n = 2 * k) then n % 2 = 0
1. By h we get k
     [obtain ⟨k, rfl⟩ := h]  we now know k : Nat, and it remains to show 2 * k % 2 = 0
2. We conclude by computation
     [omega]  that closes the goal. ∎
-/
#guard_msgs in
theorem obtain_substituting (n : Nat) (h : ∃ k, n = 2 * k) : n % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  omega

/--
info: cases_on_impossible: it is not the case that 0 = 1
1. Assume h : 0 = 1
     [intro h]  we now know h : 0 = 1, and it remains to show False
2. We conclude by h
     [cases h]  that closes the goal. ∎
-/
#guard_msgs in
theorem cases_on_impossible : (0 : Nat) ≠ 1 := by
  intro h
  cases h

/-! ## A statement is grouped the way it is bracketed -/

/--
info: bound_on_the_right: for every n : Nat, if 0 < n then 0 < 2 * n
1. We conclude by computation
     [omega]  that closes the goal. ∎
-/
#guard_msgs in
theorem bound_on_the_right (n : Nat) (h : 0 < n) : 0 < 2 * n := by
  omega

/--
info: bound_on_the_left: for every n > 0, 0 < 2 * n
1. We conclude by computation
     [omega]  that closes the goal. ∎
-/
#guard_msgs in
theorem bound_on_the_left : ∀ n > 0, 0 < 2 * n := by
  omega

/--
info: nested_implication: for all propositions P Q R, if ((P implies Q) implies R) and P and Q then R
1. Assume h : (P → Q) → R, then Assume hp : P, then Assume hq : Q
     [intro h hp hq]  we now know h : (P → Q) → R; hp : P; hq : Q, and it remains to show R
2. We conclude by h (fun _ => hq)
     [exact h (fun _ => hq)]  that closes the goal. ∎
-/
#guard_msgs in
theorem nested_implication (P Q R : Prop) : ((P → Q) → R) → (P → Q → R) := by
  intro h hp hq
  exact h (fun _ => hq)

/--
info: hypothesis_carrying_a_then: for every f : Nat → Nat, if (for all a₁ a₂ : Nat, if f a₁ = f a₂ then a₁ = a₂) then for all a b : Nat, if f a = f b then a = b
1. Fix a : Nat, then Fix b : Nat, then Assume hab : f a = f b
     [intro a b hab]  we now know a : Nat; b : Nat; hab : f a = f b, and it remains to show a = b
2. We conclude by hf using hab
     [exact hf hab]  that closes the goal. ∎
-/
#guard_msgs in
theorem hypothesis_carrying_a_then (f : Nat → Nat) (hf : Function.Injective f) :
    ∀ a b, f a = f b → a = b := by
  intro a b hab
  exact hf hab

/--
info: grouped_connectives: for every n : Nat, (n = 0 or n = 1) and n < 2 exactly when (n = 0 and n < 2) or (n = 1 and n < 2)
1. We conclude by computation
     [omega]  that closes the goal. ∎
-/
#guard_msgs in
theorem grouped_connectives (n : Nat) :
    (n = 0 ∨ n = 1) ∧ n < 2 ↔ (n = 0 ∧ n < 2) ∨ (n = 1 ∧ n < 2) := by
  omega
