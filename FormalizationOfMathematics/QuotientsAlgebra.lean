import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.RingQuot

#check Subgroup.Normal

variable (G : Type*) [Group G]
  (N : Subgroup G) [Subgroup.Normal N]

example : Type _ := G ⧸ N

#synth (Group (G ⧸ N))

example (g : G) : G ⧸ N := g

example (a b : G) :
    QuotientGroup.mk (s := N) (a * b) =
    QuotientGroup.mk a * QuotientGroup.mk b := rfl

example : G →* G⧸N := QuotientGroup.mk' N

/-!

`N` a normal subgroup of `G`, and `f : G →* H` is a morphism of groups
such that `N ≤ kernel f`.
Then there exists a unique!!! morphism `fbar : G⧸N →* H` such that
`fbar.comp QuotientGroup.mk' N = f`.

`π := QuotientGroup.mk' N`

`
G --- f ---> H
|            |
π            =
|            |
v            v
G⧸N - fbar ->H
`
-/

-- fbar
example (H : Type*) [Group H]
    (f : G →* H) (hf : N ≤ f.ker) :
    G⧸N →* H :=
  QuotientGroup.lift N f hf

example (H : Type*) [Group H]
    (f : G →* H) (hf : N ≤ f.ker) :
    (QuotientGroup.lift N f hf).comp (QuotientGroup.mk' N) = f :=
  rfl

example (H : Type*) [Group H]
    (a b : G ⧸ N →* H)
    (h : a.comp (QuotientGroup.mk' N) = b.comp (QuotientGroup.mk' N)) :
    a = b :=
  QuotientGroup.monoidHom_ext N h

/-!
`RingQuot`
-/

variable (A : Type*) [Semiring A] (r : A → A → Prop)
#synth (Semiring (RingQuot r))

example : A →+* RingQuot r := RingQuot.mkRingHom r
example (B : Type*) [Semiring B] (f : A →+* B) (hf : ∀ x y, r x y → f x = f y) :
  RingQuot r →+* B := RingQuot.preLift hf
example (B : Type*) [Semiring B] (a b : RingQuot r →+* B)
    (h : a.comp (RingQuot.mkRingHom r) = b.comp (RingQuot.mkRingHom r)) :
    a = b :=
  RingQuot.ringQuot_ext a b h

example (B : Type*) [Semiring B] (f : A →+* B) (hf : ∀ x y, r x y → f x = f y) :
    (RingQuot.lift ⟨f, hf⟩).comp (RingQuot.mkRingHom r) = f := by
  ext x
  apply RingQuot.lift_mkRingHom_apply

/-!
Quotients of Monoids
-/

variable {M : Type*} [Monoid M] (r : M → M → Prop)

inductive saturate : M → M → Prop
  | of (a b : M) : r a b → saturate a b
  | mul_compat (a a' b b' : M) : saturate a a' → saturate b b' → saturate (a * b) (a' * b')
  | refl (a : M) : saturate a a
  | symm {a b : M} : saturate a b → saturate b a
  | trans {a b c : M} : saturate a b → saturate b c → saturate a c

def MonoidQuot.setoid : Setoid M where
  r := saturate r
  iseqv := ⟨saturate.refl, saturate.symm, saturate.trans⟩

def MonoidQuot := Quotient (MonoidQuot.setoid r)

def MonoidQuot.mk : M → MonoidQuot r := Quotient.mk _

lemma MonoidQuot.mk_surjective : Function.Surjective (MonoidQuot.mk r) := by
  rintro ⟨a⟩
  exact ⟨a, rfl⟩

instance : Mul (MonoidQuot r) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
    fun _ _ _ _ h₁ h₂ => Quotient.sound <| saturate.mul_compat _ _ _ _ h₁ h₂

instance : Monoid (MonoidQuot r) where
  mul_assoc := by
    intro a b c
    obtain ⟨a,rfl⟩ := MonoidQuot.mk_surjective _ a
    obtain ⟨b,rfl⟩ := MonoidQuot.mk_surjective _ b
    obtain ⟨c,rfl⟩ := MonoidQuot.mk_surjective _ c
    apply Quotient.sound
    rw [mul_assoc]
    apply saturate.refl
  one := Quotient.mk _ 1
  one_mul := by
    intro a
    obtain ⟨a,rfl⟩ := MonoidQuot.mk_surjective _ a
    apply Quotient.sound
    rw [one_mul]
    apply saturate.refl
  mul_one := by
    intro a
    obtain ⟨a,rfl⟩ := MonoidQuot.mk_surjective _ a
    apply Quotient.sound
    rw [mul_one]
    apply saturate.refl
  npow n := Quotient.lift (fun x => Quotient.mk _ (x^n)) <| by
    intro a b h
    dsimp
    induction n with
    | zero =>
      simp only [Nat.zero_eq, pow_zero]
    | succ n ih =>
      change Quotient.mk (MonoidQuot.setoid r) (a ^ (n + 1)) =
        Quotient.mk (MonoidQuot.setoid r) (b ^ (n + 1))
      simp_rw [pow_succ]
      change MonoidQuot.mk r a * MonoidQuot.mk r (a ^ n) =
        MonoidQuot.mk r b * MonoidQuot.mk r (b ^ n)
      change MonoidQuot.mk r (a^n) = MonoidQuot.mk r (b^n) at ih
      rw [ih]
      congr 1
      apply Quotient.sound
      assumption
  npow_zero := by
    intro a
    obtain ⟨a,rfl⟩ : ∃ x, Quotient.mk (MonoidQuot.setoid r) x = a := by
      rcases a with ⟨a⟩
      use a
      rfl
    apply Quotient.sound
    simp only [pow_zero]
    apply (MonoidQuot.setoid r).refl
  npow_succ := by
    rintro n ⟨x⟩
    dsimp
    apply Quotient.sound
    rw [pow_succ]
    apply (MonoidQuot.setoid r).refl

class MulCompat {X : Type*} [Mul X] (S : Setoid X) where
  compat : ∀ x x' y y' : X, S.r x x' → S.r y y' → S.r (x * y) (x' * y')

instance (X : Type*) [Mul X] (S : Setoid X) [MulCompat S] : Mul (Quotient S) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
    fun _ _ _ _ h₁ h₂ => Quotient.sound <| MulCompat.compat _ _ _ _ h₁ h₂

instance (X : Type*) [Monoid X] (S : Setoid X) [MulCompat S] : Monoid (Quotient S) where
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ; apply Quotient.sound ; simp [mul_assoc, Setoid.refl]
  one := Quotient.mk _ 1
  one_mul := by
    rintro ⟨a⟩ ; apply Quotient.sound ; simp [Setoid.refl]
  mul_one := by
    rintro ⟨a⟩ ; apply Quotient.sound ; simp [Setoid.refl]
  npow n := Quotient.lift (fun x => Quotient.mk _ <| x^n) <| by
    intro x y h
    dsimp
    induction n with
    | zero => simp
    | succ n ih =>
      simp at ih ⊢
      simp_rw [show Nat.succ n = (n+1) from rfl, pow_succ]
      apply MulCompat.compat
      assumption'
  npow_zero := by
    rintro ⟨x⟩
    apply Quotient.sound
    simp [Setoid.refl]
  npow_succ := by
    rintro n ⟨x⟩
    apply Quotient.sound
    rw [pow_succ]

def Quotient.monoidHomLift {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) (S : Setoid M) [MulCompat S]
    (hf : ∀ (a b : M), S.r a b → f a = f b) :
    Quotient S →* N where
  toFun := Quotient.lift f hf
  map_one' := by
    change Quotient.lift _ _ (Quotient.mk _ 1) = 1
    rw [lift_mk, map_one]
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩
    change f (x * y) = f x * f y
    simp

example (M N : Type*) [Monoid M] [Monoid N] (f : M →* N) :
    MulCompat (Setoid.ker f) where
  compat x x' y y' h1 h2 := by
    change f x = f x' at h1
    change f y = f y' at h2
    change f (x * y) = f (x' * y')
    simp [map_mul, h1, h2]

/-!
# Some additional work that should be done:

0. Construct a morphism of monoids from `M` to `Quotient S` whenever `S`
  is a setoid on `M` satisfying `MulCompat S`, call it `Quotient.mkMonoidHom`.
1. Finish off the universal property of quotients of monoids:
  I.e. show that when you compose `Quotient.monoidHomLift f S` with `Quotient.mkMonoidHom S`
  you get `f` back, and show that `Quotient.monoidHomLift f S` is unique with this property.
2. Construct a complete lattice structure on the type of setoids compatible with multiplication.
3. Construct a Galois insertion between the complete lattice of such mulcompat
  setoids and the type of all setoids.
-/
