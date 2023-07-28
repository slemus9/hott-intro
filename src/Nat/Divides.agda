open import Nat.Base
import Nat.Mul as Mul
open import DependentPair using (_,_)
open import Identity using (_≡_; refl; inv)

module Nat.Divides where

one-divides-any : ∀ n -> 1 divides n
one-divides-any n = n , Mul.left-unit n

any-divides-zero : ∀ n -> n divides 0
any-divides-zero n = 0 , refl

divides-x-y-then-x+y : ∀ d x y
  -> d divides x
  -> d divides y
  -> d divides (x + y)
divides-x-y-then-x+y d x y (k1 , d*k1≡x) (k2 , d*k2≡y)
  rewrite (inv d*k1≡x) | (inv d*k2≡y) = (k1 + k2) , Mul.distrib-+-left d k1 k2
