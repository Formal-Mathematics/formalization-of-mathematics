import Mathlib

/-!

# Limits in MonoidCat

Given a diagram (i.e. a functor) `F : J ⥤ MonoidCat`, its limit, provided the limit
exists, consists of the following data:

1. An object `L : MonoidCat`.
2. For every `j : J`, a "projection" `π j : L ⟶ J.obj j`.
3. If `e : i ⟶ j` in `J` then `π i ≫ F.map e = π j`.
4. `L` is "terminal" w.r.t. 1,2,3.

2, 3 are the same thing as a natural trans from the constant functor with value `L`
to the functor `F`.
Items 1, 2, 3 are the data that is commonly called a "cone" over `F`.

-/

open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] (F : J ⥤ MonCat.{u})

def MonCat.conePt : Submonoid ((j : J) → F.obj j) where
  carrier := { x | ∀ {i j : J} (e : i ⟶ j), F.map e (x i) = x j }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry

def MonCat.Cone : Cone F where
  pt := .of <| MonCat.conePt F
  π := {
    app := fun j => {
      toFun := fun x => x.val j
      map_one' := rfl
      map_mul' := fun x y => rfl
    }
    naturality := by
      intro i j f
      dsimp
      ext ⟨x, hx⟩
      apply (hx f).symm
  }

def MonCat.IsLimit : IsLimit (MonCat.Cone F) := sorry -- condition 4.
