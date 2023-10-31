import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

/-
Let `C` be a category.:
- The terms of `C` are going to be the "objects"
- Given `X Y : C`, write `X ⟶ Y` for the type of morphisms from `X` to `Y`.
-/
variable (C : Type*) [Category C]

example (X Y : C) : Type _ := X ⟶ Y

-- The identity morphism:
example (X : C) : X ⟶ X := 𝟙 X

-- Composition of morphisms
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- Left identity
example {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
example {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp

-- Right identity
example {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f
example {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

-- Associativity
example {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h

example {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  by simp
