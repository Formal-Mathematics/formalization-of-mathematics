import Mathlib.Init.ZeroOne
import Mathlib.Data.Prod.Basic

class Monoid (M : Type) extends Mul M, One M where
  assoc : ∀ (a b c : M), a * b * c = a * (b * c)
  mul_one : ∀ (m : M), m * 1 = m
  one_mul : ∀ (m : M), 1 * m = m
  npow : M → ℕ → M 
  npow_zero : ∀ (m : M), npow m 0 = 1
  npow_succ : ∀ (m : M) (n : ℕ), npow m (n+1) = npow m n * m

def aux (X : Type) [Mul X] [One X] (x : X) : ℕ → X  
  | 0 => 1
  | (n+1) => aux X x n * x

instance : Monoid ℕ where
  mul := fun a b => a * b
  one := 1
  assoc := sorry
  mul_one := sorry
  one_mul := sorry 
  npow := aux _
  npow_zero := sorry
  npow_succ := sorry

instance monoidToPow (M : Type) [Monoid M] : Pow M ℕ where 
  pow := Monoid.npow 

instance monoidProd (A B : Type) [Monoid A] [Monoid B] : 
    Monoid (A × B) where
  mul := fun (a,b) (a', b') => (a * a', b * b')
  one := (1,1)
  assoc := sorry
  mul_one := sorry
  one_mul := sorry
  npow := fun (a,b) n => (a^n, b^n)
  npow_zero := sorry
  npow_succ := sorry

instance powProd (A B : Type) [Pow A ℕ] [Pow B ℕ] : 
    Pow (A × B) ℕ where 
  pow := fun (a,b) n => (a^n, b^n)

def pow1 (A B : Type) [Monoid A] [Monoid B] : Pow (A × B) ℕ :=  
  powProd _ _

def pow2 (A B : Type) [Monoid A] [Monoid B] : Pow (A × B) ℕ :=  
  monoidToPow _

attribute [ext] Pow

example : pow1 = pow2 := rfl