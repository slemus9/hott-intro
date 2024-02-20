import Nat.Mul as Mul
import Fin.Incl as Incl
open import Fin.Base
open import Fin.CyclicInt.Base
open import Nat hiding (add; mul; zero)
open import Identity using (_≡_; ap)

module Fin.CyclicInt.Mul where

{-
  Exercise 7.8.a
-}
incl-mul-cong : ∀ {k}
  -> (x y : ℤ/ (suc k))
  -> incl (mul x y) ≡ incl x * incl y mod (suc k)
incl-mul-cong x y = Incl.incl-map-cong (incl x * incl y)

{-
  Exercise 7.8.c

  Multiplication on Z / (k + 1) satisfies the laws of a commutative ring
-}
commutative : ∀ {k}
  -> (x y : ℤ/ (suc k))
  ->  mul x y ≡ mul y x
commutative x y = ap [_] (Mul.commutative (incl x) (incl y))
