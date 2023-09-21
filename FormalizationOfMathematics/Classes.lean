import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic


class First (α : Type) where
  a : α → ℕ 

structure First' (α : Type) where
  a : α → ℕ

example [First ℕ] : ℕ := First.a 0
example [e : First ℕ] : First.a 0 = e.a 0 := rfl

example (e : First' ℕ) : ℕ := First'.a e 0 

instance : First ℕ where
  a := fun n => n^2

instance hello : First (ℕ × ℕ) where
  a := fun (a,b) => a * b

set_option trace.Meta.synthInstance true in
def foo : ℕ := First.a (5,6) 
#check First.a

-- Why do we care about this in practice?

class FactorialRing (α : Type) [CommSemiring α] where
  factorial : α → α   

class BinomialRing (α : Type) [CommSemiring α] where
  choose : α → α → α 

def Nat.factorial : ℕ → ℕ 
  | 0 => 1 -- We will discuss this `|` notation when we talk about inductive types.
  | (n+1) => (n+1) * n.factorial

instance Nat.factorialRing : FactorialRing ℕ where
  factorial := Nat.factorial

notation t "!" => FactorialRing.factorial t

#check HSub

instance FactorialRingToBinomialRing (α : Type) [CommSemiring α] [FactorialRing α] [Sub α] [Div α] : BinomialRing α where
  choose := fun x y => x ! / (((x - y) !) * (y !))

#check Nat.factorial
#check Add.add

#check (1/4 : ℚ) + 5

--instance hereIsAName : BinomialRing ℕ where 
--  choose := fun n m => n.factorial / ((n-m).factorial * m.factorial)

notation t "choose" s => BinomialRing.choose t s

set_option trace.Meta.synthInstance true in
#eval 5 choose 2

#check add_assoc