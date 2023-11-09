import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Category.TopCat.Basic
import FormalizationOfMathematics.Categories

open CategoryTheory

variable (C D : Type*) [Category C] [Category D]

#check C ⥤ D  -- the type of functors from `C` to `D`.

variable (F : C ⥤ D)

example : C → D := F.obj
example {X Y : C} : (X ⟶ Y) → (F.obj X ⟶ F.obj Y) := F.map

example (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id X
example (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) := by simp

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g :=
  F.map_comp f g
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g :=
  by simp

/-! # Functors from the initial category.
Recall that `Empty` (the empty category) is the initial category.
-/

def Empty.functorTo (C : Type*) [Category C] :
    Empty ⥤ C where
  obj := Empty.elim
  map {X} := X.elim

-- We'll come back to what this is actually doing later on.
def Empty.functorToUnique {C : Type*} [Category C]
    (F G : Empty ⥤ C) :
    F ≅ G := NatIso.ofComponents
  (fun X => X.elim)

/-! # Functors to the final category.
Recall that `Unit` is the final category.
-/

def Unit.functorFrom (C : Type*) [Category C] :
    C ⥤ Unit where
  obj _ := .unit
  map _ := .unit

#check Iso

def Unit.functorFromUnique {C : Type*} [Category C]
    (F G : C ⥤ Unit) :
    F ≅ G := NatIso.ofComponents
  (fun X => Iso.refl _)

/-! # Forgetful functors -/

universe u

def GroupCat.forget : GroupCat.{u} ⥤ Type u where
  obj X := X
  map f := f

def TopCat.forget : TopCat.{u} ⥤ Type u where
  obj X := X
  map f := f

structure MonoidCat : Type (u+1) where
  carrier : Type u
  str : Monoid carrier

instance : CoeSort MonoidCat.{u} (Type u) where
  coe X := X.carrier

instance (X : MonoidCat.{u}) : Monoid X := X.str

instance : LargeCategory MonoidCat.{u} where
  Hom X Y := X →* Y
  id X := MonoidHom.id _
  comp f g := g.comp f

@[simps]
def MonoidCat.of (X : Type u) [Monoid X] : MonoidCat.{u} where
  carrier := X
  str := inferInstance

def GroupCat.toMonoidCat : GroupCat.{u} ⥤ MonoidCat.{u} where
  obj X := MonoidCat.of X
  map f := f

def RingCat.toMonoidCat : RingCat.{u} ⥤ MonoidCat.{u} where
  obj X := MonoidCat.of X
  map f := f.toMonoidHom

def RingCat.toAddMonoidCat : RingCat.{u} ⥤ AddMonCat.{u} where
  obj X := AddMonCat.of X
  map f := f.toAddMonoidHom
