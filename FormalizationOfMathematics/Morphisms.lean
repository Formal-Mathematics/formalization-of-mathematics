--import Mathlib.Algebra.Hom.Group.Defs
import Mathlib.Algebra.Hom.Equiv.Basic

variable (A B C : Type*) [Monoid A] [Monoid B] [Monoid C]

#check MonoidHom A B
#check A →* B

variable (f : A →* B)

#check MonoidHomClass
#check map_mul
#check map_one

#check Equiv

example (α β : Type*) : Type _ := Equiv α β 
example (α β : Type*) : Type _ := α ≃ β 

#check MulEquiv
#check A ≃* B

example (f : A ≃* B) : B ≃* A := f.symm
example : A ≃* A := .refl A
example (f : A ≃* B) (g : B ≃* C) : A ≃* C := f.trans g

example (f : A ≃* B) : A →* B := f.toMonoidHom
example (f : A ≃* B) (g : B ≃* C) : C →* A := 
  MulEquiv.toMonoidHom <| g.symm.trans f.symm

example (f : A →* C) (g : B ≃* C) : A →* B := 
  g.symm.toMonoidHom.comp f

#check MulEquivClass

#synth (MonoidHomClass (A ≃* B) A B)

example (f : A ≃* B) (a a' : A) : f (a * a') = f a * f a' := map_mul _ _ _