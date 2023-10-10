import Mathlib.Tactic
/-!
Ext = "extensionality"

The `ext` tactic applies extensionality lemmas.
-/

@[ext]
structure Foo where
  a : Nat 
  b : Nat
  h : a + b = 5

#check Foo.ext

example (x y : Foo) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  ext
  assumption'