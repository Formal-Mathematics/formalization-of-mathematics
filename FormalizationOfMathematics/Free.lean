import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Hom.Group

#check MonoidHom

example : (MonoidHom ℕ ℕ) = (ℕ →* ℕ) := rfl

example : ℕ →* ℕ where
  toFun := fun x => x^2
  map_one' := rfl
  map_mul' := fun x y => by
    dsimp
    exact Nat.mul_pow x y 2

/-
Goal: Start with a type with a multipication on it, and construct the smallest monoid on that type
with comptible multiplciation.
-/

structure Goal (X : Type) [Mul X] where
  M : Type
  inst : Monoid M
  ι : X →ₙ* M
  lift : ∀ (N : Type) [Monoid N], (X →ₙ* N) → (M →* N)
  unique : ∀ (N : Type) [Monoid N] (f g : M →* N),
    f.toMulHom.comp ι = g.toMulHom.comp ι → f = g

variable (X : Type) [Mul X]

inductive Reps where
  | of (x : X) : Reps
  | one : Reps
  | mul : Reps → Reps → Reps 

instance : One (Reps X) where
  one := .one

instance : Mul (Reps X) where
  mul := .mul

inductive Rels : Reps X → Reps X → Prop
  | mul_assoc (x y z : Reps X) : Rels ((x * y) * z) (x * (y * z))
  | one_mul (x : Reps X) : Rels (1 * x) x
  | mul_one (x : Reps X) : Rels (x * 1) x
  | of_mul (x y : X) : Rels (Reps.of (x * y)) (Reps.of x * Reps.of y)
  | mul_compat (x x' y y' : Reps X) : Rels x x' → Rels y y' → Rels (x * y) (x' * y') 
  | refl (x : Reps X) : Rels x x
  | symm (x y : Reps X) : Rels x y → Rels y x 
  | trans (x y z : Reps X) : Rels x y → Rels y z → Rels x z  

def setoid : Setoid (Reps X) where
  r := Rels _
  iseqv := by
    constructor
    · intro x 
      apply Rels.refl
    · intro x y h 
      apply Rels.symm
      assumption
    · intro x y z h1 h2 
      apply Rels.trans
      rotate_right
      exact y
      exact h1
      exact h2

def M := Quotient (setoid X)

instance : Mul (M X) where
  mul x y := Quotient.liftOn₂ x y (fun a b => Quotient.mk _ (a * b)) (by
    intro a₁ b₁ a₂ b₂ h₁ h₂   
    dsimp
    apply Quotient.sound
    apply Rels.mul_compat
    exact h₁
    exact h₂
  )

instance : Monoid (M X) where
  mul_assoc := by
    intro a b c
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    apply Quotient.sound
    apply Rels.mul_assoc
  one := sorry
  one_mul := sorry
  mul_one := sorry
