open import Fin.Base
open import Int hiding (_+_; -_)
open import Nat hiding (_+_)
open import Type

module Fin.CyclicGroups where

ℤ/_ : Nat -> Type
ℤ/ 0 = Int
ℤ/ (suc k) = Fin (Nat.suc 1)

_+_ : ∀ {k} -> ℤ/ (Nat.suc k) -> ℤ/ (Nat.suc k) -> ℤ/ (Nat.suc k)
x + y = [ Nat.add (incl x) (incl y) ]

-_ : ∀ {k} -> ℤ/ (Nat.suc k) -> ℤ/ (Nat.suc k)
-_ {k} x = [ dist (incl x) (Nat.suc k)  ]
