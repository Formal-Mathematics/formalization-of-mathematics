import Mathlib.Tactic
import Mathlib.CategoryTheory.Types

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

@[simps obj map]
def YonedaEmbedding : C ⥤ (Cᵒᵖ ⥤ Type v) where
  obj X := {
    obj := fun Y => unop Y ⟶ X
    map := fun g f => g.unop ≫ f
  }
  map {X Y} f := { app := fun Z g => g ≫ f }

/-!
TODO LIST:
1. Prove that `YonedaEmbedding` is full and faithful.
2. Prove the Yoneda Lemma: If `X : C` and `P = YonedaEmbedding.obj X` then
  `Hom(P,G) ≃ G(X)` for any `G : Cᵒᵖ ⥤ Type v`.
  Also, this equivalence is natural in `X` and `G` (but I won't prove naturality)
-/

/-! Fullness

A functor `F : C ⥤ D` is full if...
For all `X Y : C`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is surjective.
-/

#check NatTrans

instance : Full (YonedaEmbedding C) where
  preimage {X Y} η := η.app (op X) <| 𝟙 _
  witness := by
    intro X Y η
    ext T g : 3
    have := η.naturality
    dsimp [YonedaEmbedding] at g ⊢
    specialize this g.op
    dsimp at this
    replace this := congr_fun this (𝟙 X)
    dsimp at this
    replace this := this.symm
    convert this
    simp

/-!
A functor `F : C ⥤ D` is faiththful if for all `X Y : C`
the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is injective.
-/

instance : Faithful (YonedaEmbedding C) where
  map_injective := by
    intro X Y a b h
    suffices a = ((YonedaEmbedding C).map a).app _ (𝟙 _) by
      rw [this, h]
      simp
    simp

/-!
The Yoneda Lemma:

If `X : C` and `P = YonedaEmbedding.obj X` then
  `Hom(P,G) ≃ G(X)` for any `G : Cᵒᵖ ⥤ Type v`.
-/

def YonedaLemma (X : C) (G : Cᵒᵖ ⥤ Type v) :
    ((YonedaEmbedding C).obj X ⟶ G) ≃ G.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app := fun T e => G.map e.op ξ }
  left_inv η := by
    ext T g : 3
    simpa using congr_fun (η.naturality g.op) (𝟙 _) |>.symm
  right_inv ξ := by simp

/-!
Exercises:
1. Prove that `YonedaLemma` is natural in `X`.
2. Prove that `YonedaLemma` is natural in `G`.
-/
