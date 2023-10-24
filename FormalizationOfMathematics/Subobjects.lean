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

@[simp]
lemma Submonoid'.mem_coe (H : Submonoid' M) (m : M) :
  m ∈ H.carrier ↔ m ∈ H := Iff.rfl

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

#synth (PartialOrder (Submonoid' M))

instance : InfSet (Submonoid' M) where
  sInf S := {
    carrier := sInf (Submonoid'.carrier '' S)
    one_mem' := by
      simp only [Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter]
      intro H _
      apply H.one_mem
    mul_mem' := by
      intro x y hx hy
      simp only [Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter, Submonoid'.mem_coe] at hx hy ⊢
      intro H hH
      apply H.mul_mem
      · specialize hx H hH ; exact hx -- forward reasoning
      · apply hy ; assumption -- backward reasoning
  }

@[simp]
lemma Submonoid'.mem_sInf (S : Set (Submonoid' M)) (m : M) :
    (m ∈ sInf S) ↔ (∀ H : Submonoid' M, H ∈ S → m ∈ H) := by
  change m ∈ sInf (Submonoid'.carrier '' S) ↔ _
  simp

  --show m ∈ sInf (Submonoid'.carrier '' S) ↔ _ by simp

instance : CompleteLattice (Submonoid' M) :=
  completeLatticeOfInf _ <| by
    intro S -- the goal here is a conjunction, use the `constructor` tactic.
    constructor
    · intro H hH x hx
      simp only [Submonoid'.mem_sInf] at hx
      apply hx
      assumption
    · intro H hH x hx
      dsimp [lowerBounds] at hH
      simp only [Submonoid'.mem_sInf]
      intro L hL
      apply hH
      assumption'

/-!
Next goal: Define a Galois insertion between `Submonoid' M` and `Set M`.
-/

def Submonoid'.closure (S : Set M) : Submonoid' M :=
  sInf { H | S ≤ H }

lemma Submonoid'.closure_induction {motive : M → Prop} {S : Set M}
    (m : M) (hm : m ∈ Submonoid'.closure S)
    (hS : ∀ s, s ∈ S → motive s)
    (hone : motive 1)
    (hmul : ∀ a b : M, motive a → motive b → motive (a * b)) :
    motive m := by
  let H : Submonoid' M := {
    carrier := { m | motive m }
    one_mem' := hone
    mul_mem' := hmul
  }
  have hH : closure S ≤ H := by
    intro x hx
    dsimp [closure] at hx
    simp only [mem_sInf, Set.mem_setOf_eq] at hx
    apply hx
    intro y hy
    apply hS
    exact hy
  change m ∈ H
  apply hH
  exact hm

variable (L : Type*) [Monoid L]

#check @Submonoid'.carrier M _
#check Submonoid'.carrier (M := L)

variable (M) in
lemma Submonoid'.gc : GaloisConnection Submonoid'.closure (Submonoid'.carrier (M := M)) := by
  intro A B
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro x hx
    simp only [mem_coe]
    apply h
    dsimp [closure]
    simp only [mem_sInf, Set.mem_setOf_eq]
    intro H hH
    apply hH
    assumption
  · intro x hx
    dsimp [closure] at hx
    simp only [mem_sInf, Set.mem_setOf_eq] at hx
    apply hx
    exact h

variable (M) in
def Submonoid'.gi : GaloisInsertion Submonoid'.closure (Submonoid'.carrier (M := M)) where
  choice S _ := Submonoid'.closure S
  gc := Submonoid'.gc M
  le_l_u := sorry
  choice_eq S hS := rfl
