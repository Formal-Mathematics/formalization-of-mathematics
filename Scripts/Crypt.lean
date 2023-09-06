import Lean
import Mathlib.Data.Nat.Digits

open Lean

def ALPHABET := "!@#$%^&*()_+1234567890-=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
def LEN := ALPHABET.length
def MODULUS : Nat := 75833231818474540109969139305905899925421762951050157077451924669380020981053

def Char.index? (c : Char) : Option Nat := 
  ALPHABET.toList.indexOf? c

def Char.index! (c : Char) : Nat := 
  c.index?.get!

def String.toAlphabetArray (s : String) : List ℕ := do
  s.toList.map Char.index!

def String.encode (s : String) : Nat := Id.run <| do
  let s := s.toAlphabetArray
  let mut out := 0
  let mut e := 0
  for c in s do
    out := out + c * LEN^e
    e := e + 1
  return out

def Nat.decode (n : Nat) : String := Id.run <| do
  let digits := Nat.digits LEN n 
  let mut out := ""
  for d in digits do
    out := out.push ALPHABET.toList[d]!
  return out

def Nat.binary (n : Nat) := Nat.digits 2 n

def Fin.powAux (f : Fin (n+1)) (k : Nat) : Fin (n+1) := 
match k with 
  | 0 => f
  | (k+1) => Fin.ofNat <| (f.powAux k).val^2

def Fin.pow (f : Fin (n+1)) (k : Nat) : Fin (n+1) := Id.run <| do
  let digits := k.binary
  let mut out := 1
  for h : i in [:digits.length] do
    have := h.2
    if digits[i] == 0 then continue
    out := out * f.powAux i
  return out

def Nat.inverseMod (a m : Nat) : Nat := 
  if a.gcd m != 1 then 0 else ((a.xgcd m).fst % m).natAbs

def main (args : List String) : IO Unit := do
  let some cmd := args[0]? | throw <| .userError "Usage: crypt (d/e) password text"
  let some password := args[1]? | throw <| .userError "Usage: crypt (d/e) password text"
  let some text := args[2]? | throw <| .userError "Usage: crypt (d/e) password text"
  let text : Fin MODULUS := .ofNat <| text.encode % MODULUS
  IO.println text
  let key := 
    if cmd == "e" 
    then password.encode % (MODULUS - 1)  
    else (password.encode % (MODULUS - 1)).inverseMod (MODULUS - 1)
  let out := text.pow key
  IO.println (out.val % MODULUS).decode