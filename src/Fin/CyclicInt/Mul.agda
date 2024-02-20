import Fin.Incl as Incl
open import Fin.Base
open import Fin.CyclicInt.Base
open import Nat hiding (add; mul; zero)

module Fin.CyclicInt.Mul where

{-
  Exercise 7.8.a
-}
mul-incl-cong : ∀ {k}
  -> (x y : ℤ/ (suc k))
  -> incl (mul x y) ≡ incl x * incl y mod (suc k)
mul-incl-cong x y = Incl.incl-map-cong (incl x * incl y)
