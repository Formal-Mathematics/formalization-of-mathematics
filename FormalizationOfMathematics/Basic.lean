import FormalizationOfMathematics.Init
import Mathlib -- Mathlib is Lean4's formalized mathematics library


#check ℕ  
#check Type -- the collection of all "sets"
#check 37
#check "hello world"
#check 'c'
#check List ℕ  
#check [1,2,3]

#check ℚ

#check (1/5)
#eval (1/5) -- similar to Python's 1//5
#eval ((1 : ℚ) / 5) * 5

#check ℕ → ℕ

-- In mathematics, n ↦ n^2 is a function from ℕ to ℕ.   
-- In Lean:
#check fun n : ℕ ↦ n^2
#check λ (n : ℕ) => n^2

-- In math, we use the symbol `f : A → B`  

#check [[1,2,3],[3,4,5]]

#check [(1 : ℚ),2,3][5]?

#check Fin
#eval ![2,3,4] 1

#check !![1,2;2,3]

#check Type
#check Prop

section
variable (P : Prop)

#check P

example (h1 h2 : P) : h1 = h2 := rfl
end

example : 0 < 1 := zero_lt_one

-- Dependent Propositions

#check (3 % 2 = 0) ∨ (3 % 2 = 1)

#check ∀ (n : ℕ), (n % 2 = 0) ∨ (n % 2 = 1) 
#check (n : ℕ) → (n % 2 = 0) ∨ (n % 2 = 1) 

#check @Fin