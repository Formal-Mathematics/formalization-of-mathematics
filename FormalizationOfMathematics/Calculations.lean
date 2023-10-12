import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

variable (G : Type) [Group G]

#check congr_arg
#check congr_fun

example (a b x : G) (h : a * x = b) : x = a⁻¹ * b := by
  replace h : a⁻¹ * (a * x) = a⁻¹ * b := 
    congr_arg (fun y => a⁻¹ * y) h
  rwa [← mul_assoc, inv_mul_self, one_mul] at h

example (a b x : G) (h : a * x = b) : x = a⁻¹ * b := by
  apply_fun (fun x => a⁻¹ * x) at h
  rwa [← mul_assoc, inv_mul_self, one_mul] at h

example (a b x : G) (h : a * x = b) : x = a⁻¹ * b := by
  rw [← h, ← mul_assoc, inv_mul_self, one_mul]

example (a b x : G) (h : a * x = b) : x = a⁻¹ * b := by
  simp only [← h, inv_mul_cancel_left]

example (a b c d : G) : 
    (a * b)⁻¹ * (c⁻¹ * d)⁻¹ = b⁻¹ * (d * a)⁻¹ * c := by
  simp only [mul_inv_rev, inv_inv, mul_assoc]

example (a b c d : G) : 
    (a * b)⁻¹ * (c⁻¹ * d)⁻¹ = b⁻¹ * (d * a)⁻¹ * c := by
  simp_rw [mul_inv_rev, inv_inv]
  simp_rw [mul_assoc]

-- group
example (a b c d : G) : 
    (a * b)⁻¹ * (c⁻¹ * d)⁻¹ = b⁻¹ * (d * a)⁻¹ * c := by
  group

-- abel
example (a b c d : H) [AddCommGroup H] : 
    -(a + b) - (-c + d) = c - (d + a) + (-b) := by
  abel

#check mul_assoc
example (a b c d e f : G) 
    (h₁ : a⁻¹ * c = e * d⁻¹) 
    (h₂ : b⁻¹ * e = e * f) :
    (a * b)⁻¹ * c * d = e * f := by
  rwa [mul_inv_rev, mul_assoc b⁻¹, h₁, mul_assoc, mul_assoc,
    inv_mul_self, mul_one]

example (a b c d e f : G) 
    (h₁ : a⁻¹ * c = e * d⁻¹) 
    (h₂ : b⁻¹ * e = e * f) :
    (a * b)⁻¹ * c * d = e * f := by
  rw [mul_inv_rev]
  conv_lhs => 
    congr
    rw [mul_assoc]
  rw [h₁]
  simp [mul_assoc, h₂]

-- calc
example (a b c d e f : G) (h₁ : a⁻¹ * c = e * d⁻¹) (h₂ : b⁻¹ * e = e * f) :
    (a * b)⁻¹ * c * d = e * f := 
  calc (a * b)⁻¹ * c * d
    _ = (b⁻¹ * a⁻¹) * c * d := by rw [mul_inv_rev]
    _ = b⁻¹ * (a⁻¹ * c) * d := by simp only [mul_assoc]
    _ = b⁻¹ * (e * d⁻¹) * d := by rw [h₁]
    _ = b⁻¹ * e * (d⁻¹ * d) := by simp only [mul_assoc]
    _ = b⁻¹ * e * 1 := by simp only [inv_mul_self]
    _ = b⁻¹ * e := by simp only [mul_one]
    _ = e * f := h₂

example (a b c d e f : G) (h₁ : a⁻¹ * c = e * d⁻¹) (h₂ : b⁻¹ * e = e * f) :
    (a * b)⁻¹ * c * d = e * f := by
  calc (a * b)⁻¹ * c * d
    _ = (b⁻¹ * a⁻¹) * c * d := by rw [mul_inv_rev]
    _ = b⁻¹ * (a⁻¹ * c) * d := by simp only [mul_assoc]
    _ = b⁻¹ * (e * d⁻¹) * d := by rw [h₁]
    _ = b⁻¹ * e * (d⁻¹ * d) := by simp only [mul_assoc]
    _ = b⁻¹ * e * 1 := by simp only [inv_mul_self]
    _ = b⁻¹ * e := by simp only [mul_one]
    _ = e * f := h₂
  
-- congrm
example (a b b' c : G) (h : b = b') : a * b * c = a * b' * c := by
  congrm a * ?_ * ?_
  exact h
  rfl

-- calc + congrm
example (a b c d e f : G) (h₁ : a⁻¹ * c = e * d⁻¹) (h₂ : b⁻¹ * e = e * f) :
    (a * b)⁻¹ * c * d = e * f := 
  calc (a * b)⁻¹ * c * d
    _ = b⁻¹ * (a⁻¹ * c) * d := by group
    _ = b⁻¹ * (e * d⁻¹) * d := by
      congrm _ * ?_ * _
      exact h₁
    _ = b⁻¹ * e := by group
    _ = e * f := h₂

example (a b c d : R) [CommRing R] :
    (a + b) * (c + d)^2 = 
    (c + d) * b * (c + d) + (a * c^2+ 2 * c * a * d + d^2 * a) := by
  have : ∀ (x : R), x^2 = x * x := by
    intro x
    exact sq x
  simp only [sq]
  simp only [add_mul, mul_add]
  ring

-- ring
example (a b c d : R) [CommRing R] :
    (a + b) * (c + d)^2 = 
    (c + d) * b * (c + d) + (a * c^2+ 2 * c * a * d + d^2 * a) := by
  rw [show (c + d)^2 = c^2 + 2 * c * d + d^2 by ring]
  ring

-- field_simp
example (x y z : F) [Field F] (h₁ : z ≠ 0) (h₂ : 1 - z ≠ 0):
    (x + y/z) + x * z/(1 - z) = (x - y)/(1-z) + y/(z * (1-z)) := by
  field_simp
  ring