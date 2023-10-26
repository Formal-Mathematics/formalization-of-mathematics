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

instance : Monoid (MonoidQuot r) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
    fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound <| saturate.mul_compat _ _ _ _ h₁ h₂
  mul_assoc := sorry
  one := Quotient.mk _ 1
  one_mul := sorry
  mul_one := sorry
  npow n := Quotient.lift (fun x => Quotient.mk _ (x^n)) sorry
  npow_zero := sorry
  npow_succ := sorry
