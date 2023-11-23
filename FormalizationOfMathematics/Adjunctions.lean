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

instance (M : MonoidCat.{u}) : Monoid ((forget MonoidCat).obj M) :=
  inferInstanceAs (Monoid M)

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
    (fun x y => .mk _ <| x * y) <| by
      intro a₁ a₂ b₁ b₂ h₁ h₂
      apply Quotient.sound
      apply Rels.mul_compat
      assumption'
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    apply Quotient.sound
    apply Rels.mul_assoc
  one := Quotient.mk _ 1
  one_mul := by
    rintro ⟨⟩
    apply Quotient.sound
    apply Rels.one_mul
  mul_one := by
    rintro ⟨⟩
    apply Quotient.sound
    apply Rels.mul_one

def FreeMonoid.preLift (M : Type u) [Monoid M] (f : X → M) :
    Reps X → M
  | .of x => f x
  | .one => 1
  | .mul a b => FreeMonoid.preLift _ f a * FreeMonoid.preLift _ f b

@[simp]
lemma FreeMonoid.preLift_mul {M : Type u} [Monoid M] (f : X → M)
    (x y : Reps X) : preLift _ _ f (x * y) = preLift _ _ f x * preLift _ _ f y := rfl

@[simp]
lemma FreeMonoid.preLift_one {M : Type u} [Monoid M] (f : X → M) :
  preLift _ _ f 1 = 1 := rfl

@[simp]
lemma FreeMonoid.preLift_of {M : Type u} [Monoid M] (f : X → M) (x : X) :
  preLift _ _ f (.of x) = f x := rfl


def FreeMonoid.liftFun (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid X → M :=
  Quotient.lift
    (FreeMonoid.preLift _ _ f) <| by
      intro a b h
      induction h with
      | mul_assoc x y z => simp [mul_assoc]
      | mul_one x => simp
      | one_mul x => simp
      | mul_compat x x' y y' _ _ h1 h2 => simp [h1,h2]
      | rfl x => rfl
      | symm _ h => exact h.symm
      | trans _ _ h1 h2 => exact h1.trans h2

def FreeMonoid.lift (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid X →* M where
  toFun := FreeMonoid.liftFun _ _ f
  map_one' := rfl
  map_mul' := by rintro ⟨x⟩ ⟨y⟩ ; rfl

def FreeMonoid.incl : X → FreeMonoid X :=
  fun x => Quotient.mk _ <| .of x

lemma FreeMonoid.incl_lift (M : Type u) [Monoid M] (f : X → M) :
    FreeMonoid.lift X _ f ∘ (FreeMonoid.incl X) = f := rfl

lemma FreeMonoid.hom_ext (M : Type u) [Monoid M] (f g : FreeMonoid X →* M)
    (h : f ∘ FreeMonoid.incl X = g ∘ FreeMonoid.incl X) : f = g := by
  sorry

lemma FreeMonoid.lift_comp_incl
    (X : Type u) (M : Type u) [Monoid M] (f : FreeMonoid X →* M) :
    FreeMonoid.lift _ _ (f ∘ FreeMonoid.incl _) = f := by
  apply FreeMonoid.hom_ext
  rw [incl_lift]

lemma FreeMonoid.lift_comp {X X' Y : Type u} [Monoid Y] (f : X → X') (g : X' → Y) :
    lift _ _ (g ∘ f) = (lift X' Y g).comp (lift X (FreeMonoid X') (incl _ ∘ f)) := by
  apply FreeMonoid.hom_ext
  dsimp
  rw [incl_lift, Function.comp.assoc, incl_lift, ← Function.comp.assoc, incl_lift]

lemma FreeMonoid.comp_comp_incl {X Y Y' : Type u} [Monoid Y] [Monoid Y']
    (f : FreeMonoid X →* Y) (g : Y →* Y') :
    (g ∘ f) ∘ incl X = g ∘ f ∘ incl X := rfl

lemma FreeMonoid.lift_incl {X : Type u} :
    lift _ _ (incl X) = .id _ := by
  apply FreeMonoid.hom_ext
  rfl

lemma FreeMonoid.lift_comp' {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    lift _ _ (incl Z ∘ g ∘ f) = (lift _ _ (incl _ ∘ g)).comp (lift _ _ (incl _ ∘ f)) := by
  apply FreeMonoid.hom_ext
  dsimp
  rw [Function.comp.assoc]
  sorry

end

@[simps]
def MonoidCat.free : Type u ⥤ MonoidCat.{u} where
  obj X := MonoidCat.of <| FreeMonoid X
  map {X Y} f := FreeMonoid.lift _ _ <| FreeMonoid.incl _ ∘ f
  map_id := by
    intro X
    apply FreeMonoid.lift_incl
  map_comp := by
    intro X Y Z f g
    apply FreeMonoid.lift_comp'

@[simps]
def MonoidCat.adjEquiv (X : Type u) (M : MonoidCat.{u}) :
    (free.obj X ⟶ Y) ≃ (X ⟶ (forget MonoidCat).obj Y) where
  toFun f :=
    letI f : free.obj X →* Y := f
    f ∘ FreeMonoid.incl _
  invFun f := FreeMonoid.lift _ _ f
  left_inv _ := FreeMonoid.lift_comp_incl ..
  right_inv _ := FreeMonoid.incl_lift ..

def MonoidCat.coreHomEquiv : Adjunction.CoreHomEquiv free (forget MonoidCat) where
  homEquiv X M := adjEquiv X M
  homEquiv_naturality_left_symm := by
    intro X X' Y f g
    apply FreeMonoid.lift_comp
  homEquiv_naturality_right := by
    intro X Y Y' f g
    apply FreeMonoid.comp_comp_incl

def MonoidCat.freeAdj : MonoidCat.free.{u} ⊣ forget MonoidCat.{u} :=
  Adjunction.mkOfHomEquiv coreHomEquiv
