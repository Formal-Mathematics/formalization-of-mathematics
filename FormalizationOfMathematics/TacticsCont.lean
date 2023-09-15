import Mathlib.Tactic
import Lean
import Scripts.GPT
import Std.Tactic.TryThis

-- Functional Programming in Lean4

open Lean Elab Meta Tactic -- opens various namespaces

/-
syntax "testing" : tactic

elab_rules : tactic
  | `(tactic|testing) => withMainContext do
    let currentGoal ← getMainGoal 
    let goalState ← Meta.ppGoal currentGoal
    let lctx ← getLCtx
    for i in lctx do
      logInfo i.type
      logInfo i.userName

lemma foo (n m : ℕ) (f : ℕ → ℕ) : n + 1 = 1 + n := by
  testing
-/

example (n m : ℕ) (f : ℕ → ℕ) : f n + m = m + f n := by
  apply add_comm