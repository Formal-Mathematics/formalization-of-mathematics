import Mathlib.Tactic

variable (X : Type*) (S T : Set X)

example (h : S ⊆ T) : ∀ x, x ∈ S → x ∈ T := h

example (x : X) (hx : x ∈ S) (h : S ⊆ T) : x ∈ T := by
  apply h
  assumption

example (x : X) (hx : x ∈ S) (h : S ⊆ T) : x ∈ T := by
  apply h at hx
  assumption

example : (S ⊆ T) ↔ (S ≤ T) := Iff.rfl

variable (F : Type*) [SetLike F X]

example (S T : F) : Prop := S ≤ T
example (S T : F) : (S ≤ T) ↔ ((S : Set X) ⊆ (T : Set X)) := Iff.rfl


example (x : X) (S T : F) (h : S ≤ T) (hx : x ∈ S) : x ∈ T := by
  apply h
  assumption

example (x : X) (S T : F) (h : S ≤ T) (hx : x ∈ S) : x ∈ T := by
  apply h at hx
  assumption
