import Mathlib.GroupTheory.Subgroup.Basic

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

#check Coe
instance (H : Submonoid' M) : Monoid H where
  mul := fun x y => {
    val := x * y
    property := H.mul_mem _ _ (Submonoid'.property x) (Submonoid'.property y)
  }
  mul_assoc := sorry 
  one := {
    val := 1
    property := H.one_mem
  }
  one_mul := sorry
  mul_one := sorry
  npow n h := {
    val := (h : M)^n
    property := sorry
  }
  npow_zero := sorry
  npow_succ := sorry