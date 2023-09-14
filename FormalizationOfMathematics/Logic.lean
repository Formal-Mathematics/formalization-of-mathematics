import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Basic

section

-- Logical And

variable (X Y : Type) (P Q : Prop)

example (x : X) (y : Y) : X × Y := 
  Prod.mk x y

example (hP : P) (hQ : Q) : P ∧ Q := 
  And.intro hP hQ

end

section

-- Logical or

variable (X Y : Type) (P Q : Prop)

example (x : X) : X ⊕ Y := 
  Sum.inl x

example (hP : P) : P ∨ Q :=  
  Or.inl hP

example (y : Y) : X ⊕ Y := 
  Sum.inr y

example (hQ : Q) : P ∨ Q :=  
  Or.inr hQ

end

section

-- Universal quantification

variable (α : Type) (P : α → Prop) (X : α → Type)

example (h : ∀ a, X a) : (a : α) → X a :=  
  fun a => h a

example (h : ∀ a, P a) : ∀ a : α, P a := 
  fun a => h a

end

section

-- Existential quantification

variable (α : Type) (P : α → Prop) (X : α → Type)

example (a : α) (x : X a) : Σ a : α, X a :=
  Sigma.mk a x

example (a : α) (h : P a) : ∃ a : α, P a := 
  Exists.intro a h


end

section

-- Implication

variable (P Q : Prop)

example (hP : P) (h : P → Q) : Q := 
  h hP

end 

section

-- Negation

variable (P : Prop)

example : Prop := ¬ P 

example : (¬P) ↔ (P → False) := Iff.rfl

end

section

-- True and False as propositions

example : Prop := False

example : Prop := True

example : True := trivial

example (P : Prop) : False → P := False.elim 

end

section

-- Predicates and relations

/-

In usual mathematics, if `S` is a set and `B` is a subset, we can obtain 
a predicate `P` on `S` which defines `B`, so `P` is a proposition which depends on
elements of `S`, which characterizes `B`.

I.e. `P x = (x ∈ B)` for `x : S`.
-/

#check Set ℕ 

/-
If `X : Type`, then `Set X` denotes the type of subsets of `X`,
such subsets are modeled as predicates on `X`.
-/

-- The set of all perfect squares in `ℕ`  
example : Set ℕ := fun n => ∃ m : ℕ, m^2 = n 
example : Set ℕ := { n : ℕ | ∃ m : ℕ, m^2 = n } 

-- these two are the SAME by DEFINITION
example : { n : ℕ | ∃ m : ℕ, m^2 = n } = (fun n : ℕ => ∃ m : ℕ, m^2 = n) := rfl

variable (α γ : Type)

example (A B : Set α) : Set α := A ∩ B 
example (A B : Set α) : (A ∩ B) = { x : α | (x ∈ A) ∧ (x ∈ B) } := rfl
example (A B : Set α) : (A ∪ B) = { x : α | (x ∈ A) ∨ (x ∈ B) } := rfl

example (A : Set α) (x : α) : Prop := x ∈ A 
example (A : Set α) (x : α) : (x ∈ A) ↔ (A x) := Iff.rfl

-- This is the union of the family `S`.
example (S : γ → Set α) : Set α := { x : α | ∃ g : γ, (x ∈ S g) } 
-- This is the intersection of the family `S`.
example (S : γ → Set α) : Set α := { x : α | ∀ g : γ, (x ∈ S g) } 

-- The empty set
example : Set α := ∅ 
example : Set α := ⊥
example : (∅ : Set α) = { _x : α | False } := rfl
example : (∅ : Set α) = (⊥ : Set α) := rfl

-- The largest subset (the one which includes all elements)
example : Set α := ⊤ 
example : (⊤ : Set α) = { _x : α | True } := rfl 

end

section

-- Relations

/-
Recall (in mathematics): A relation `R` on a set `X` is just a subset `R ⊆ X × X`  
We write `x R y` to denote the property that `(x,y) ∈ R`. 
-/

variable (X : Type) (R : Set (X × X))

example (x y : X) : Prop := (x,y) ∈ R

-- Recall that `R` is really a predicate `X × X → Prop`, so we can "curry" and obtain 
-- a function `X → X → Prop`.  


-- In Lean, we almost always model relations as functions `X → X → Prop`

-- Similarly, we can model 3-fold relations as `X → X → X → Prop`.

-- The type of equivalence relations on a type `X` is called `Setoid X`.
example : Type := Setoid X
example (S : Setoid X) : Type := Quotient S
-- ^^ we'll come back to quotients next week.

end 

section

-- Cyrrying
-- The jargon: This is the adjunction between the binary product functor and the 
-- internal hom.

variable (X Y Z : Type)

example (f : X × Y → Z) : X → Y → Z := 
  fun x y => f (x,y)

example (f : X → Y → Z) : X × Y → Z :=  
  fun (x,y) => f x y

#check Equiv.curry
end