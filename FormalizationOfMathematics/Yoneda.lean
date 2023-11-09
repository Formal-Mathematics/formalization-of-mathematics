import Mathlib.CategoryTheory.Yoneda

open CategoryTheory

universe v u
variable (C : Type u) [Category.{v} C]

/-!
# The opposite category

Given a category `C`, the opposite category `Cᵒᵖ` has the same objects as `C`, but
given `X Y : Cᵒᵖ`, `X ⟶ Y := (unop Y) ⟶ (unop X)`, where `unop X : C` is the object `X : Cᵒᵖ`.
-/

open Opposite

example (X Y : C) (f : X ⟶ Y) : op Y ⟶ op X := f.op
example (X Y : Cᵒᵖ) (f : X ⟶ Y) : unop Y ⟶ unop X := f.unop

/-!
The Yoneda embedding is a functor from `C` to the type of functors
`C ⥤ Type v`.
-/

#check NatTrans

def YonedaEmbedding : C ⥤ (Cᵒᵖ ⥤ Type v) where
  obj X := {
    obj := fun Y => unop Y ⟶ X
    map := fun g f => g.unop ≫ f
  }
  map {X Y} f := { app := fun Z g => g ≫ f }
