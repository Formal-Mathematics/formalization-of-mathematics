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