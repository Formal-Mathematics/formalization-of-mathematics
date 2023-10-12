import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

class MyGroup (G : Type) extends One G, Mul G, Inv G where
  mul_assoc : ∀ (x y z : G), (x * y) * z = x * (y * z)
  one_mul : ∀ (x : G), 1 * x = x
  mul_one : ∀ (x : G), x * 1 = x
  inv_mul_self : ∀ (x : G), x⁻¹ * x = 1
  mul_inv_self : ∀ (x : G), x * x⁻¹ = 1

namespace MyGroup

attribute [simp] 
  mul_assoc
  one_mul
  mul_one
  inv_mul_self
  mul_inv_self

variable (G : Type) [MyGroup G]

@[simp]
lemma inv_mul_cancel_right (a b : G) : a⁻¹ * (a * b) = b := by
  simp only [← mul_assoc, inv_mul_self, one_mul]

@[simp]
lemma mul_inv_cancel_right (a b : G) : a * (a⁻¹ * b) = b := by
  simp only [← mul_assoc, mul_inv_self, one_mul]

#check Iff
variable {G}
lemma eq_iff_mul_eq (c a b : G) : a = b ↔ c * a = c * b := by
  constructor
  · intro h  
    rw [h]
  · intro h
    apply_fun (fun e => c⁻¹ * e) at h
    simpa only [← mul_assoc, inv_mul_self, one_mul] using h

lemma eq_iff_eq_mul (c a b : G) : a = b ↔ a * c = b * c := by
  constructor
  · intro h ; rw [h] 
  · intro h ; apply_fun (fun e => e * c⁻¹) at h
    simpa only [mul_assoc, mul_inv_self, mul_one] using h

@[simp]
lemma inv_mul_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [eq_iff_mul_eq (a * b), mul_inv_self] 
  have := calc a * b * (b⁻¹ * a⁻¹)
    _ = a * (b * b⁻¹) * a⁻¹ := by simp only [mul_assoc]
    _ = a * 1 * a⁻¹ := by simp only [mul_inv_self]
    _ = 1 := by simp
  rw [this]

@[simp]
lemma inv_inv (a : G) : a⁻¹⁻¹ = a := sorry

macro "my_group" : tactic => 
  `(tactic|simp only [mul_assoc, one_mul, mul_one, inv_mul_self, 
    mul_inv_self, inv_mul_cancel_right, 
    mul_inv_cancel_right, inv_mul_rev, inv_inv])

example (a b c d : G) : 
    (a * b)⁻¹ * (c⁻¹ * d)⁻¹ = b⁻¹ * (d * a)⁻¹ * c := by
  my_group