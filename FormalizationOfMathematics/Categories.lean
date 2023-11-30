import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.CategoryTheory.Category.Preorder
--import Mathlib.CategoryTheory.DiscreteCategory

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

/-! # Examples! -/

/-! Coleton says the empty is the simplest one: -/

-- The empty type:

#check Empty
#check Empty.elim

instance : SmallCategory Empty where
  Hom X := X.elim
  id X := X.elim
  comp {X} := X.elim

-- The category of types

universe u
#check Type u

#check fun (X Y : Type u) => X → Y

/-
-- Writing `Category.{u} C` means that
-- for `X Y : C`, `X ⟶ Y : Type u`.
instance : LargeCategory (Type u) where
  Hom X Y := X → Y
  id X := id
  comp {X Y Z} f g := g ∘ f

-- The category of groups.

variable (G : Type*) [Group G]

structure GroupCat where
  carrier : Type u
  str : Group carrier

instance : CoeSort GroupCat (Type _) where
  coe G := G.carrier

instance (G : GroupCat) : Group G := G.str

instance : LargeCategory GroupCat.{u} where
  Hom X Y := X →* Y
  id X := MonoidHom.id _
  comp f g := g.comp f

-/

-- The final category (the category with one object and one morphism)

#check Unit
#check PUnit

instance : SmallCategory Unit where
  Hom _ _ := Unit
  id _ := .unit
  comp _ _ := .unit

-- Partial Orders

#check PLift
#check PLift.down
#check PLift.up

#check ULift
#check ULift.down
#check ULift.up

/-
instance (X : Type u) [PartialOrder X] : SmallCategory X where
  Hom a b := ULift (PLift (a ≤ b))
  id a := .up <| .up <| le_refl a
  comp {a b c} f g := .up <| .up <| le_trans f.down.down g.down.down
  id_comp := by intros ; rfl
  comp_id := by intros ; rfl
  assoc := by intros ; rfl
-/

variable (X : Type u) [Preorder X]
#synth (SmallCategory X)

example (a b : X) (h : a ≤ b) : a ⟶ b := h.hom
example (a b : X) (h : a ≤ b) : h.hom = .up (.up h) := rfl

example (a b : X) (f : a ⟶ b) : a ≤ b := f.le
example (a b : X) (f : a ⟶ b) : f.le = f.down.down := rfl

-- Discrete categories: These are categories where the only
-- morphisms are the identity morphisms.

structure Discrete (X : Type u) : Type u where
  as : X

instance (X : Type u) : SmallCategory (Discrete X) where
  Hom a b := ULift (PLift <| a.as = b.as)
  id a := .up <| .up <| rfl
  comp {a b c} f g := .up <| .up <| f.down.down.trans g.down.down

-- `Fin n`
