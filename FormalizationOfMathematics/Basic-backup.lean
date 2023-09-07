import Mathlib.Data.Nat.Basic -- Mathlib is Lean4's formalized mathematics library
import Mathlib.Data.Rat.Basic 
import Mathlib.Data.Matrix.Notation 

--#set_pandoc_options "-V" "theme=dark"
--#clear_pandoc_options


/-!

# Types

-/

#check ℕ
#check ℤ
#check ℚ

#check ℕ × ℤ  
#check ℕ → ℤ
#check ℕ ⊕ ℤ 

variable (X Y : Type) in
#check X × Y  

variable (X Y : Type) in
#check X ⊕ Y  

variable (X Y : Type) in
#check X → Y  

#check Type
#check Type 1
#check Type 2

universe u in
#check Type u

#check Fin
#check (n : ℕ) → Fin n  
#check Σ (n : ℕ), Fin n
#check (n : ℕ) × Fin n

variable (α : Type) (X : α → Type) in section
#check (a : α) → X a
#check Σ (a : α), X a
end

variable (α : Type u) (X : α → Type v) in 
set_option pp.universes true in section

#check Σ (a : α), X a
#check (a : α) → X a
end

/-!

# Sorts

-/

#check Sort 0
#check Sort 1

variable (P : Prop) in
#check show Sort 0 from P

variable (P Q : Prop) in section
#check P → Q 
#check P ∧ Q 

end

#check ∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
#check ∃ a b : ℕ, a + b = 3

#check (n : ℕ) → n % 2 = 0 ∨ n % 2 = 1
--!!
#check Σ' (a b : ℕ), a + b = 3

example : (∃ a b : ℕ, a + b = 3) ↔ Nonempty (Σ' (a b : ℕ), a + b = 3) := by
  constructor
  · intro h
    obtain ⟨a,b,h⟩ := h  
    exact ⟨a,b,h⟩ 
  · intro h 
    obtain ⟨a,b,h⟩ := h 
    exact ⟨a,b,h⟩ 

example : (∃ a b : ℕ, a + b = 3) ↔ Nonempty (Σ' (a b : ℕ), a + b = 3) := .intro 
  (fun ⟨a,b,h⟩ => ⟨a,b,h⟩) 
  (fun ⟨a,b,h⟩ => ⟨a,b,h⟩)

/-!
# Functions
-/

#check ℕ → ℚ 

def div : ℕ → ℚ := λ n => 1/n
#eval div 3

#check Fin 4

def thing : (n : ℕ) → Fin (n + 1) := fun n => if n == 0 then 0 else 1
def another : (n : ℕ) → Fin (n + 1)
  | 0 => 0
  | _ => 1

#eval thing 4
#check thing 4

#eval thing 0
#check thing 0

#eval another 0
#check another 0

#eval another 1
#check another 1

def exerciseI1 (α : Type u) (X : α → Type v) : 
    ((a : α) → X a) ≃ { f : α → ((a : α) × X a) // Sigma.fst ∘ f = id } := 
  sorry

structure Function.splitting (f : α → β) where
  σ : β → α  
  hσ : f ∘ σ = id

def exerciseI2 (α : Type u) (X : α → Type v) :
    ((a : α) → X a) ≃ (Sigma.fst : (a : α) × X a → α).splitting := 
  sorry

def hintI (α : Type u) (X : α → Type v) :
    ((a : α) → X a) ≃ { g // (Sigma.fst : (a : α) × X a → α).LeftInverse g } where
  toFun f := ⟨fun a => ⟨a, f a⟩, fun _ => rfl⟩ 
  invFun := fun ⟨g,hg⟩ a => hg a ▸ (g a).snd
  left_inv _ := rfl
  right_inv _ := Subtype.ext <| funext fun _ => Sigma.eq _ rfl |>.symm

def exerciseII (α β γ : Type*) : (α → β → γ) ≃ (α × β → γ) := sorry

def hintII (α β γ : Type*) : (α × β → γ) ≃ (α → β → γ) := 
  sorry  -- Try using `by exact?`... Can you use this to obtain `exerciseII`? 

/-!
# Predicates and Relations
-/

section Predicates

variable (X : Type u) (P Q : X → Prop)

#check X → Prop 
#check { x : X | P x }

example : ({ x | P x } ⊆ { x | Q x }) ↔ (∀ x, P x → Q x) := Iff.rfl

example : Set X = (X → Prop) := rfl

end Predicates