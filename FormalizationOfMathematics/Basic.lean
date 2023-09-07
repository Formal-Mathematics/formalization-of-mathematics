import Mathlib.Data.Nat.Basic -- Mathlib is Lean4's formalized mathematics library
import Mathlib.Data.Rat.Basic 
import Mathlib.Data.Matrix.Notation 


#check ℕ  
#check Type -- the collection of all "sets"
#check 37
#check "hello world"
#check 'c'
#check List ℕ  
#check [1,2,3]

#check ℚ

#check (1/5)
#eval (1/5) -- similar to Python's 1//5
#eval ((1 : ℚ) / 5) * 5

#check ℕ → ℕ

-- In mathematics, n ↦ n^2 is a function from ℕ to ℕ.   
-- In Lean:
#check fun n : ℕ ↦ n^2
#check λ (n : ℕ) => n^2

-- In math, we use the symbol `f : A → B`  

#check [[1,2,3],[3,4,5]]

#check [(1 : ℚ),2,3][5]?

#check Fin
#eval ![2,3,4] 1

#check !![1,2;2,3]

#check Type
#check Prop

section
variable (P : Prop)

#check P

example (h1 h2 : P) : h1 = h2 := rfl
end

example : 0 < 1 := zero_lt_one

-- Dependent Propositions

#check (3 % 2 = 0) ∨ (3 % 2 = 1)

#check ∀ (n : ℕ), (n % 2 = 0) ∨ (n % 2 = 1) 
#check (n : ℕ) → (n % 2 = 0) ∨ (n % 2 = 1) 

#check @Fin


/-
Last time: 
- A type is a thing that contains terms.
- If `T` is a type, we write `t : T` to indicate that `t` is 
  a term of type `T`.

- Slogan: `:` = `is a`
- `37 : ℕ` `37 is a Nat`. 
- `-4 : ℤ` `-4 is an Int`. 
- `"hello world" : String` `"hello world" is a String`.

- The CH correspondence: Think about propositions as types,
  where a term of a proposition is a proof of that proposition.

- In Lean: we have the notion of a `Sort`
-/

#check Sort 0
-- Sort 0 is the same thing as Prop

#check Prop -- the collection of all propositions.
#check Type -- the collection of all types.

/-!
# DEPENDENT FUNCTIONS
-/

section
variable (X Y : Type)
#check X → Y 
#check (fun n ↦ 1/n : ℕ → ℚ)
end

-- In a dependent function `f`, the codomain can depend on
-- the input.

section

variable (α : Type)
variable (β : α → Type)
#check (a : α) → β a  

end

section
/-
Think about the function which takes `n : ℕ` as an input,
and returns `n` as an element of `{0,1,...,n} = Fin (n+1)`. 
-/

example : (n : ℕ) → Fin (n+1) := fun n => n

end

section

/-!
How to construct types from other types?
-/


-- Binary Product
example (A B : Type) : Type := A × B
example (a : A) (b : B) : A × B := (a,b)

-- Binary Disjoint Union
example (A B : Type) : Type := A ⊕ B
example (A B : Type) (a : A) : A ⊕ B := Sum.inl a
example (A B : Type) (b : B) : A ⊕ B := Sum.inr b

-- Products of a family of types
example (α : Type) (X : α → Type) : Type := (a : α) → X a
example (α : Type) (X : α → Type) 
  (x : ∀ (a : α), X a) : (a : α) → X a := x 

/-
In math, if (X_a)_{a : α} is a family of sets, the product 
Π_a, X a has the universal property: 

if Z is any set, and `f_a : Z → X_a` is a family of functions 
indexed by `a : α`, then there is a unique function 
`f : Z → Π a, X a` such that the composition of `f` with 
the projection `Π a, X a → X a` is `f_a` for any `a : α`. 
-/

example (α : Type) (X : α → Type) (Z : Type)
    (f : (a : α) → (Z → X a)) : Z → ((a : α) → X a) := 
  fun z a => f a z

-- Disjoint unions of families of types
example (α : Type) (X : α → Type) : Type := Σ a, X a
example (α : Type) (X : α → Type) : Type := (a : α) × (X a)

example (α : Type) (X : α → Type) (a : α) (x : X a) : 
    Σ a, X a := 
  Sigma.mk a x

/-
In math, if (X_a)_{a : α} is a family of sets, the disjoint union 
Σ a, X a has the universal property: 

if Z is any set, and `f_a : X_a → Z` is a family of functions 
indexed by `a : α`, then there is a unique function 
`f : Σ a, X a → Z` such that the composition of `f` with 
the inclusions `X a → Σ a, X a` is `f_a` for any `a : α`. 
-/

#check Sigma.fst
example (α : Type) (X : α → Type) (Z : Type)
    (f : (a : α) → (X a → Z)) : (Σ a, X a) → Z := 
  fun ⟨a,x⟩ => f a x

/-
Suppose I have a family of sets X_a, indexed by a : α, 
consider the projection π : (Σ a, X a) → α 
suppose I take a "section" of π, meaning a function σ : α → (Σ a, X a), 
such that the composition π ∘ σ = id.  

I claim that such a section corresponds to a dependent function (a : α) → X a.
-/

example (α : Type) (X : α → Type) : 
    ((a : α) → X a) ≃ { σ : α → (Σ a, X a) | ∀ a : α, (σ a).fst = a } where
  toFun f := ⟨fun a => Sigma.mk a (f a), sorry⟩ 
  invFun := fun ⟨σ, hσ⟩ a => 
    let t := (σ a)
    hσ a ▸ t.snd
  left_inv := sorry
  right_inv := sorry


end