import Mathlib

variable {α β} (f : α → β) (S : Set α) (T : Set β)

-- The image of `S` under `f`
example : Set β := f '' S

example (a : α) (ha : a ∈ S) : f a ∈ f '' S :=
  by exact Set.mem_image_of_mem f ha

example (b : β) (hb : b ∈ f '' S) :
    ∃ (a : α), a ∈ S ∧ f a = b :=
  hb

example (b : β) (hb : b ∈ f '' S) : ∃ a : α, f a = b := by
  obtain ⟨a, _, rfl⟩ := hb
  use a

-- The preimage of `T` under `f`
example : Set α := f ⁻¹' T

example (a : α) (ha : f a ∈ T) : a ∈ f ⁻¹' T :=
  ha

-- The range of a function

example : Set β := Set.range f

example (b : β) (hb : b ∈ Set.range f) :
    ∃ a : α, f a = b :=
  hb

example : f '' ⊤ = Set.range f := by
  simp only [Set.top_eq_univ, Set.image_univ]

-- Inclusions

example (A B : Set α) : Prop := A ≤ B

example (A B : Set α) : (A ≤ B) ↔ (∀ x : α, x ∈ A → x ∈ B) := Iff.rfl
