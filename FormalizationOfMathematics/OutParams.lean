import Mathlib

#check Valued

class MyFun (A : Type) (B : outParam Type) where
  f : A → B

instance idFun (X : Type) : MyFun X X where
  f := id

def square (M : Type) [Monoid M] : MyFun M M where
  f := fun x => x^2

example (n : ℕ) : ℕ := MyFun.f n 
#eval MyFun.f 5

example (n : ℕ) : ℕ := 
  let _ : MyFun ℕ ℕ := square _
  MyFun.f n

#check @(fun (n : ℕ) =>
  let _ : MyFun ℕ ℕ := square _
  MyFun.f n)

#check @(fun (n : ℕ) =>
  letI _ : MyFun ℕ ℕ := square _
  MyFun.f n)

instance (X Y : Type) : MyFun (X × Y) X where
  f := Prod.fst

set_option trace.Meta.synthInstance true in
example (n : Nat) := MyFun.f n 