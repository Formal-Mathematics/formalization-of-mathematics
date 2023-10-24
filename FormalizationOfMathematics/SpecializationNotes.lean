import Mathlib.Tactic

variable {α γ : Type*} {β : α → Type*} (f : {a : α} → β a → γ)

example {a : α} (b : β a) : γ := f b
example {a : α} := @f a
example {a : α} := f (a := a)
