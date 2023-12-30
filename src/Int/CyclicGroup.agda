open import Fin using (Fin)
open import Int.Base using (Int)
open import Nat using (Nat)
open import Type using (Type)

module Int.CyclicGroup where

ℤ/_ : Nat -> Type
ℤ/ Nat.zero = Int
ℤ/ Nat.suc k = Fin (Nat.suc k)
