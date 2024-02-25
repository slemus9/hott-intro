open import Fin.Base
open import Int.Base using (Int)
open import Nat.Base hiding (zero; add; mul)
open import Type.Base

module Fin.CyclicInt.Base where

ℤ/_ : Nat -> Type
ℤ/ 0 = Int
ℤ/ (suc k) = Fin (suc k)

zero : ∀ {k} -> Fin (suc k)
zero = first

add : ∀ {k} -> ℤ/ (suc k) -> ℤ/ (suc k) -> ℤ/ (suc k)
add x y = [ incl x + incl y ]

{-
  Example on Fin 6
  1. inv $ i (i (i (i (i (base {0}))))) = [ 6 ] = i (i (i (i (i (base {0}))))) --> 0 + 6 = 6
  2. inv $ i (i (i (i (base {1})))) = [ 5 ] = base {5} --> 1 + 5 = 6
  3. inv $ i (i (i (base {2}))) = [ 4 ] = i (base {4}) --> 2 + 4 = 6
  4. inv $ i (i (base {3})) = [ 3 ] = i (i (base {3})) --> 3 + 3 = 6
  5. inv $ i (base {4}) = [ 2 ] = i (i (i (base {2}))) --> 4 + 2 = 6
  6. inv $ base {5} = [ 1 ] = i (i (i (i (base {1})))) --> 5 + 1 = 6

  If I add any ℤ/ (suc k) with its inv application, I should always get the first element
-}
inv : ∀ {k} -> ℤ/ (suc k) -> ℤ/ (suc k)
inv {k} x = [ dist (incl x) (suc k) ]

mul : ∀ {k} -> ℤ/ (suc k) -> ℤ/ (suc k) -> ℤ/ (suc k)
mul x y = [ incl x * incl y ]
