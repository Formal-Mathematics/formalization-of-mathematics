/- Implicit Variables-/
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Nat.Basic

structure Foo (α : Type) where
  a : α

-- alpha is implicit
def g (α : Type) (t : Foo α) := t.a

#check Foo.a

variable (t : Foo ℕ)

#check g _ t

def first {α : Type} {n : ℕ} (x : Fin (n+1) → α) : α := 
  x 0 

#eval first ![10,1,2,3]