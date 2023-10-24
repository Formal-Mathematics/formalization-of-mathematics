import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Ring.Equiv

/-! Some notes-/

-- About morphisms
-- Classes
#check FunLike
#check MonoidHomClass
#check RingHomClass

-- Morphisms themselves
#check ∀ {α β}, α → β
#check MonoidHom
#check RingHom

-- About equivalences
#check EquivLike
#check MulEquivClass
#check RingEquivClass

#check ∀ {α β}, α ≃ β
#check MulEquiv
#check RingEquiv

/-!

The `SetLike` class.

-/

-- Thinking about subsets as types via the subtype construction

example {X : Type*} (S : Set X) : Type _ := S
example {X : Type*} (S : Set X) (x : X) (hx : x ∈ S) : S :=
  ⟨x, hx⟩ --Subtype.mk x hx

example {X : Type*} (S : Set X) (x : S) : X := x
example {X : Type*} (S : Set X) (x : S) : ↑x ∈ S := x.property

example {T X : Type*} [SetLike T X] (S : T) : Type _ := S
example {T X : Type*} [SetLike T X] (S : T) (x : X) : Prop := x ∈ S
example {T X : Type*} [SetLike T X] (S : T) (s : S) : X := s
example {T X : Type*} [SetLike T X] (S : T) (s : S) : ↑s ∈ S := by exact SetLike.coe_mem s

variable (M : Type*) [Monoid M]

@[ext]
structure Submonoid' where
  carrier : Set M
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ (x y : M), x ∈ carrier → y ∈ carrier → x * y ∈ carrier

/-
example (H : Submonoid' M) (m : M) : Prop := m ∈ H.carrier -- we want to write `m ∈ H`.
example (H : Submonoid' M) : Type _ := sorry -- we want to just write H
example (H : Submonoid' M) : Monoid sorry := sorry -- we want to say `Monoid H`, but we can't.
-/

#check SetLike

instance : SetLike (Submonoid' M) M where
  coe N := N.carrier
  coe_injective' := by
    intro A B h
    ext1 -- this will apply `Submonoid'.ext`.
    --apply Submonoid'.ext
    exact h

variable {M}
lemma Submonoid'.mul_mem {H : Submonoid' M} (x y : M)
    (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
  H.mul_mem' _ _ hx hy

#check Membership
lemma Submonoid'.property {H : Submonoid' M} (h : H) : ↑h ∈ H :=
  h.2

lemma Submonoid'.one_mem (H : Submonoid' M) : 1 ∈ H := H.one_mem'

example (H : Submonoid' M) (m : M) : Prop := m ∈ H
example (H H' : Submonoid' M) (h : ∀ m : M, m ∈ H ↔ m ∈ H') : H = H' :=
  SetLike.ext h

example (H : Submonoid' M) : Type _ := H

example (H : Submonoid' M) (h : H) : M := h

@[simps]
instance (H : Submonoid' M) : Mul H where
  mul a b := ⟨a * b, H.mul_mem _ _ (Submonoid'.property a) (Submonoid'.property b)⟩

@[simps]
instance (H : Submonoid' M) : One H where
  one := ⟨1, H.one_mem⟩

instance (H : Submonoid' M) : Monoid H where
  mul_assoc := by
    intro a b c
    ext
    dsimp
    apply mul_assoc
  one_mul := by
    intro a
    ext
    dsimp
    apply one_mul
  mul_one := by
    intro a
    ext
    dsimp
    apply mul_one
  npow n m := {
    val := (m : M)^n
    property := by
      induction n with
      | zero =>
        simp only [Nat.zero_eq, pow_zero]
        exact H.one_mem
      | succ n ih =>
        change (m : M) ^ (n+1) ∈ H
        rw [pow_succ]
        apply H.mul_mem
        · exact m.property
        · assumption }
  npow_zero := by
    intro m
    ext
    simp
  npow_succ := by
    intro m n
    ext
    dsimp
    apply pow_succ

def Submonoid'.subtype (H : Submonoid' M) : H →* M where
  toFun m := m
  map_one' := rfl
  map_mul' _ _ := rfl

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  cases hx with
  | intro x' hx' =>
    cases hy with
    | intro y' hy' =>
      use x' * y'
      rw [map_mul, hx', hy']

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  rcases hx with ⟨x',hx'⟩
  rcases hy with ⟨y',hy'⟩
  use x' * y'
  rw [map_mul, hx', hy']

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  obtain ⟨x',hx'⟩ := hx
  obtain ⟨y',hy'⟩ := hy
  use x' * y'
  rw [map_mul, hx', hy']

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  obtain ⟨x',rfl⟩ := hx
  obtain ⟨y',rfl⟩ := hy
  use x' * y'
  rw [map_mul]

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  rcases hx with ⟨x',rfl⟩
  rcases hy with ⟨y',rfl⟩
  use x' * y'
  rw [map_mul]

example {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (x y : B) (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f := by
  dsimp [Set.range] at hx hy ⊢
  rcases hx with ⟨x',rfl⟩
  rcases hy with ⟨y',rfl⟩
  refine ⟨x' * y', ?_⟩
  simp

def MonoidHom.range' {A B : Type*} [Monoid A] [Monoid B] (f : A →* B) :
    Submonoid' B where
  carrier := Set.range f
  one_mem' := by
    use 1
    exact f.map_one
  mul_mem' := by
    rintro x y ⟨x',rfl⟩ ⟨y',rfl⟩
    use x' * y'
    simp

/-! The order structure on subobjects -/

instance : InfSet (Submonoid' M) where
  sInf S := {
    carrier := sInf (Submonoid'.carrier '' S)
    one_mem' := sorry
    mul_mem' := sorry
  }

instance : CompleteLattice (Submonoid' M) :=
  completeLatticeOfInf (Submonoid' M) <| by
    intro S
    dsimp [IsGLB, IsGreatest]
    refine ⟨?_, ?_⟩
    · dsimp [lowerBounds]
      intro A hA x hx
      sorry
    · sorry
