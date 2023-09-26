import Mathlib.Tactic

/- A type with a single element -/

inductive SingleElement where
  | point : SingleElement

example (a b : SingleElement) : a = b := 
  match a, b with
    | .point, .point => rfl

example (a b : SingleElement) : a = b := by 
  cases a with
  | point => 
    cases b with
    | point => rfl

inductive TwoElement where
  | point1 : TwoElement
  | point2 : TwoElement

def TwoElementEquivBool : TwoElement ≃ Bool where
  toFun 
    | .point1 => true
    | .point2 => false
  invFun 
    | true => .point1
    | false => .point2
  left_inv := by
    intro x
    cases x with
    | point1 => rfl
    | point2 => rfl
  right_inv := by
    intro x
    cases x with
    | false => rfl
    | true => rfl

#check TwoElement.rec

def foo : TwoElement → ℕ 
  | .point1 => 1
  | .point2 => 2

/- The natural numbers -/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat 

#print prefix MyNat

#check Nat

def factorial : Nat → Nat 
  | 0 => 1
  | n+1 => (n + 1) * factorial n

def fib : Nat → Nat 
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

#eval fib 10

/- Inductive types with parameters -/

inductive MyList (α : Type) where
  | nil : MyList α 
  | cons : α → MyList α → MyList α    

#check MyList
#check List

def List.length' {α : Type} : List α → ℕ := fun
  | .nil => 0
  | .cons _ tail => tail.length' + 1

def List.const {α : Type} (a : α) : ℕ → List α := fun
  | .zero => [] 
  | .succ n => .cons a (List.const a n)

lemma List.const_succ {α : Type} (a : α) (n : ℕ) : 
    List.const a (n+1) = (a :: List.const a n) :=
  rfl

lemma List.length_const {α : Type} {a : α} {n : ℕ} : 
    (List.const a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [List.const_succ, List.length_cons, ih]

/- Inductive Functions -/

inductive Fin' : ℕ → Type  
  | zero (n : ℕ) : Fin' (n+1)
  | succ (n : ℕ) : Fin' n → Fin' (n+1)

example : Fin' 2 ≃ Bool where
  toFun := fun
    | .zero _ => false
    | .succ _ (.zero _) => true
  invFun := fun
    | .false => .zero _
    | .true => .succ _ (.zero _)
  left_inv := sorry
  right_inv := sorry

-- Exercise
example (n : ℕ) : Fin' n ≃ Fin n := sorry

/- Inductive Propositions -/

section

variable {M : Type} [Monoid M]

inductive gen (S : Set M) : M → Prop
  | of (m : M) (hm : m ∈ S) : gen S m
  | one : gen S 1
  | mul (m n : M) : gen S m → gen S n → gen S (m * n) 

def gen' (S : Set M) : Set M := gen S

example (H : Submonoid M) (S : Set M) (h : S ⊆ H) : 
    gen' S ⊆ (H : Set M) := by 
  intro x hx
  induction hx with
    | of m hm => 
      apply h
      assumption
    | one => 
      exact one_mem H
    | mul m n _ _ hh1 hh2 =>
      apply H.mul_mem <;> assumption

end

/- Quotients -/

#check Quot
#check Quotient
