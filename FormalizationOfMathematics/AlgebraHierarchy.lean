import Mathlib.Data.Finsupp.Basic

/-!
The Algebraic Hierarchy
-/

variable (M N : Type*) [Monoid M] [Monoid N]

structure MonoidHom' where
  toFun : M → N  
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = toFun x * toFun y

instance thisOne : MonoidHomClass (MonoidHom' M N) M N where
  coe f := f.toFun
  coe_injective' := sorry
  map_mul f := f.map_mul
  map_one f := f.map_one

set_option trace.Meta.synthInstance true in
#synth (MonoidHomClass (MonoidHom' M N) M N)

example (f : MonoidHom' M N) (m n : M) : f (m * n) = f m * f n := 
  f.map_mul _ _

example (f : MonoidHom' M N) (m n : M) : f (m * n) = f m * f n := 
  map_mul _ _ _

example (f : MonoidHom' M N) (m : M) : N := f m

variable (A B : Type*) [Semiring A] [Semiring B]

structure SemiringHom' extends MonoidHom' A B where
  map_zero : toFun 0 = 0 
  map_add : ∀ (a b : A), toFun (a + b) = toFun a + toFun b

instance : RingHomClass (SemiringHom' A B) A B where
  coe f := f.toFun
  coe_injective' := sorry
  map_mul f := f.map_mul
  map_one f := f.map_one
  map_add f := f.map_add
  map_zero f := f.map_zero

example (f : SemiringHom' A B) (a : A) : B := f a

example (f : SemiringHom' A B) (a b : A) : f (a * b) = f a * f b := 
  map_mul _ _ _