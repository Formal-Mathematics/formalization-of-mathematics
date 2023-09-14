import Mathlib.Tactic

/-!
In a nutshell, a tactic is a program which tells lean how to construct terms.

In practice, we use tactics primarily for constructing proofs (i.e. terms of propositions)
while we construct terms of non-propostition types by hand.

To use tactics in Lean4, we have the `by` keyword.
-/

example : 1 + 1 = 2 := by rfl

example (n : ℕ) : 1 + n = n + 1 := by 
  sorry

example (P Q R : Prop) (hP : P) (h : P → Q) (h' : Q → R) : R := by
  exact h' (h hP)

example (P Q R : Prop) (hP : P) (h : P → Q) (h' : Q → R) : R := by
  apply h'
  apply h
  exact hP

example (P Q R : Prop) (hP : P) (h : P → Q) (h' : Q → R) : R := by
  apply h'
  apply h
  assumption

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro h h' hP
  apply h'
  apply h
  assumption

example (n : ℕ) : 0 + n = n := by
  cases n with
  | zero => 
    rfl
  | succ n => 
    sorry

example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    change Nat.succ (0 + n) = _
    rw [ih] 