import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Hom.Group

section scratchwork

variable (M : ℕ → Type) [∀ n, Monoid (M n)]

example : Monoid (M 37) := inferInstance

end scratchwork

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
  ι_lift : ∀ (N : Type) [Monoid N] (f : X →ₙ* N),
    (lift N f).toMulHom.comp ι = f
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

#check M

instance : Mul (M X) where
  mul := Quotient.lift₂ (fun a b => Quotient.mk _ (a * b)) (by
    intro a₁ b₁ a₂ b₂ h₁ h₂   
    dsimp
    apply Quotient.sound
    apply Rels.mul_compat
    exact h₁
    exact h₂
  )

instance : One (M X) where
  one := Quotient.mk _ .one

instance : Monoid (M X) where
  --mul := sorry
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ 
    apply Quotient.sound
    apply Rels.mul_assoc
  --one := sorry
  one_mul := by
    rintro ⟨a⟩ 
    apply Quotient.sound
    apply Rels.one_mul
  mul_one := by
    rintro ⟨a⟩ 
    apply Quotient.sound
    apply Rels.mul_one

def ιFun : X → M X := fun x => Quotient.mk _ (.of x)

def ι : X →ₙ* M X where
  toFun := ιFun X
  map_mul' := by 
    intro x y 
    apply Quotient.sound
    apply Rels.of_mul

def liftFunReps (N : Type) [Monoid N] (f : X →ₙ* N) :
    Reps X → N 
  | .of x => f x
  | .one => 1
  | .mul x y => liftFunReps _ f x * liftFunReps _ f y

@[simp]
lemma liftFunReps_of (N : Type) [Monoid N] (f : X →ₙ* N) (x : X) :
    liftFunReps X N f (.of x) = f x := 
  rfl

@[simp]
lemma liftFunReps_one (N : Type) [Monoid N] (f : X →ₙ* N) :
    liftFunReps X N f 1 = 1 := 
  rfl

@[simp]
lemma liftFunReps_mul (N : Type) [Monoid N] (f : X →ₙ* N) (x y : Reps X) :
    liftFunReps X N f (x * y) = liftFunReps X N f x * liftFunReps X N f y := 
  rfl

def liftFun (N : Type) [Monoid N] (f : X →ₙ* N) :
    M X → N := 
  Quotient.lift (liftFunReps _ _ f) <| by
    intro a b h
    induction h with
    | mul_assoc x y z => simp [mul_assoc]
    | one_mul x => simp
    | mul_one x => simp
    | of_mul x y => 
      dsimp
      apply f.map_mul
    | mul_compat x x' y y' _ _ h₁ h₂ => simp [h₁,h₂]
    | refl x => rfl
    | symm x y _ h => exact h.symm
    | trans x y z _ _ h₁ h₂ => exact h₁.trans h₂

def lift (N : Type) [Monoid N] (f : X →ₙ* N) :
    M X →* N where
  toFun := liftFun _ _ f
  map_one' := rfl
  map_mul' := by rintro ⟨x⟩ ⟨y⟩ ; rfl

@[simp]
lemma QuotMk_RepsOne : Quot.mk (setoid X).r (Reps.one) = (1 : M X) := rfl 

def solution : Goal X where
  M := M X
  inst := inferInstance
  ι := ι X
  lift := lift X
  ι_lift := by
    intro N _ f
    rfl
  unique := by
    intro N _ f g h
    ext ⟨x⟩
    induction x with
    | of x => 
      apply_fun (fun e => e x) at h
      exact h
    | one => 
      dsimp
      rw [f.map_one, g.map_one]
    | mul x y h₁ h₂ => 
      let x' : M X := Quotient.mk _ x
      let y' : M X := Quotient.mk _ y
      change f x' = g x' at h₁
      change f y' = g y' at h₂
      change f (x' * y') = g (x' * y')
      rw [f.map_mul, g.map_mul, h₁, h₂]