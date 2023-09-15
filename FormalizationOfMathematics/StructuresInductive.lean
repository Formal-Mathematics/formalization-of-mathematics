import Mathlib.Tactic
import Scripts.GPT
-- Structures

/-!

Defining Monoids as an example of a structure

A monoid is a Type `M` endowed with a binary operation `*` which is associative, 
and such that there exists some `1 : M` which is a two-sided unit for `*`.

-/

#check PSigma
#check Sigma

def MonoidTypeAsSigma := 
  Σ' (M : Type) (op : M → M → M) (one : M),
    (∀ a b c : M, op (op a b) c = op a (op b c)) ∧ 
    (∀ a : M, op one a = a) ∧ 
    (∀ a : M, op a one = a)

-- Think of this as the type of all monoids
structure MonoidType where
  M : Type
  op : M → M → M 
  one : M
  assoc : ∀ (a b c : M), op (op a b) c = op a (op b c)
  left_id : ∀ (a : M), op one a = a
  right_id : ∀ (a : M), op a one = a

#check MonoidType

-- The type of all monoid structures on a given type `M`.
structure Monoid' (M : Type) where
  op : M → M → M 
  one : M
  assoc : ∀ (a b c : M), op (op a b) c = op a (op b c)
  left_id : ∀ (a : M), op one a = a
  right_id : ∀ (a : M), op a one = a

variable (M : Type)
#check Monoid' M

example : Monoid' ℕ where
  op := (· + ·)
  one := 0
  assoc := by exact fun a b c => Nat.add_assoc a b c
  left_id := by exact fun a => Nat.zero_add a
  right_id := by exact fun a => rfl

example : Monoid' ℕ where
  op := (· * ·)
  one := 1
  assoc := by exact fun a b c => Nat.mul_assoc a b c
  left_id := by exact fun a => Nat.one_mul a
  right_id := by apply Nat.mul_one
 
/-!

Typeclass is a special structure that Lean considers as a class.
A class is a structure, terms of which, lean is able to look for automatically.

-/

class Monoid'' (M : Type) where
  op : M → M → M 
  one : M
  assoc : ∀ (a b c : M), op (op a b) c = op a (op b c)
  left_id : ∀ (a : M), op one a = a
  right_id : ∀ (a : M), op a one = a

#check Monoid'.op

example (M : Type) (isMonoid : Monoid' M) (x y : M) : M := 
  isMonoid.op x y

example (M : Type) [Monoid'' M] (x y : M) : M := 
  Monoid''.op x y

class Monoid''' (M : Type) extends Mul M, One M where
  assoc : ∀ (a b c : M), (a * b) * c = a * (b * c)
  left_id : ∀ (a : M), 1 * a = a
  right_id : ∀ (a : M), a * 1 = a

example (M : Type) [Monoid''' M] (x y : M) : M := x * y

/-!
Fin
-/

#check Fin

structure Fin' (n : ℕ) where
  val : ℕ
  val_lt : val < n

#check Fin'.mk

example (n m : ℕ) (h : m < n) : Fin' n := 
  Fin'.mk m h

example (n m : ℕ) (h : m < n) : Fin' n where
  val := m
  val_lt := h

example (n m : ℕ) (h : m < n) : Fin' n := 
  ⟨m, h⟩

example : Monoid' ℕ := 
  ⟨(· + ·), 0, add_assoc, zero_add, add_zero⟩ 

/-!
Next time:
1. Implicit variables `{x : X}` (`⦃x : X⦄`)
2. Typeclass parameters `[Group G]` `[Monoid G]`, etc., and the typeclass system.
3. Inductive types, like ℕ, Lists, etc. 
-/