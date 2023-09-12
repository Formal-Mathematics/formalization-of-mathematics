
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