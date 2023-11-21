import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Group.Hom.Defs

open CategoryTheory

/-!

# Adjunctions

Given two categories `C` and `D`, and functors `F : C ⥤ D` and
`G : D ⥤ C` an adjunction `F ⊣ G` consists of equivalences

`(F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)`

for all `X : C` and `Y : D`,

where these equivalences are "natural" in `X` and `Y`.

-/

/-!
Extended Example: An adjunction between the category of monoids and the category of types.
-/

universe u

structure MonoidCat where
  carrier : Type u
  str : Monoid carrier

instance : CoeSort MonoidCat.{u} (Type u) where
  coe M := M.carrier

instance (M : MonoidCat) : Monoid M := M.str

def MonoidCat.of (M : Type u) [Monoid M] : MonoidCat.{u} :=
  ⟨M, inferInstance⟩

instance : LargeCategory MonoidCat.{u} where
  Hom X Y := X →* Y
  id X := MonoidHom.id _
  comp f g := g.comp f

instance : ConcreteCategory.{u} MonoidCat.{u} where
  forget := {
    obj := fun M => M
    map := fun {M N} f => f.toFun
  }
  forget_faithful := {
    map_injective := by
      intro X Y f g h
      dsimp at h
      apply MonoidHom.ext
      intro x
      exact congr_fun h x
  }

example : MonoidCat.{u} ⥤ Type u := forget MonoidCat

/-!
The free construction
-/

section

variable (X : Type u)

inductive Reps where
  | of : X → Reps
  | one : Reps
  | mul : Reps → Reps → Reps

instance : One (Reps X) where one := .one
instance : Mul (Reps X) where mul := .mul

inductive Rels : Reps X → Reps X → Prop where
  | mul_assoc (x y z : Reps X) : Rels ((x * y) * z) (x * (y * z))
  | mul_one (x : Reps X) : Rels (x * 1) x
  | one_mul (x : Reps X) : Rels (1 * x) x
  | mul_compat (x x' y y' : Reps X) :
      Rels x x' → Rels y y' → Rels (x * y) (x' * y')
  | rfl (x : Reps X) : Rels x x
  | symm {x y : Reps X} : Rels x y → Rels y x
  | trans {x y z : Reps X} : Rels x y → Rels y z → Rels x z

def FreeMonoidSetoid : Setoid (Reps X) where
  r := Rels _
  iseqv := ⟨Rels.rfl, Rels.symm, Rels.trans⟩

def FreeMonoid := Quotient (FreeMonoidSetoid X)

instance : Monoid (FreeMonoid X) where
  mul := Quotient.lift₂
    (fun x y => .mk _ <| x * y)
    sorry
  mul_assoc := sorry
  one := Quotient.mk _ 1
  one_mul := sorry
  mul_one := sorry

def FreeMonoid.preLift (M : Type u) [Monoid M] (f : X ⟶ M) :
    Reps X → M
  | .of x => f x
  | .one => 1
  | .mul a b => FreeMonoid.preLift _ f a * FreeMonoid.preLift _ f b

def FreeMonoid.liftFun (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid X → M :=
  Quotient.lift
    (FreeMonoid.preLift _ _ f)
    sorry

def FreeMonoid.lift (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid X →* M where
  toFun := FreeMonoid.liftFun _ _ f
  map_one' := sorry
  map_mul' := sorry

def FreeMonoid.incl : X → FreeMonoid X :=
  fun x => Quotient.mk _ <| .of x

lemma FreeMonoid.incl_lift (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid.lift X _ f ∘ (FreeMonoid.incl X) = f := sorry

lemma FreeMonoid.hom_ext (M : Type u) [Monoid M] (f g : FreeMonoid X ⟶ M)
    (h : f ∘ FreeMonoid.incl X = g ∘ FreeMonoid.incl X) : f = g :=
  sorry

end

def MonoidCat.free : Type u ⥤ MonoidCat.{u} where
  obj X := MonoidCat.of <| FreeMonoid X
  map {X Y} f := FreeMonoid.lift _ _ <| FreeMonoid.incl _ ∘ f
  map_id := sorry
  map_comp := sorry

def MonoidCat.coreHomEquiv : Adjunction.CoreHomEquiv free (forget MonoidCat) where
  homEquiv := sorry
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

def MonoidCat.freeAdj : MonoidCat.free.{u} ⊣ forget MonoidCat.{u} :=
  Adjunction.mkOfHomEquiv coreHomEquiv
