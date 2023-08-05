open import Nat.Base
import Nat.Add as Add
import Nat.Mul as Mul
import Nat.Dist as Dist
open import DependentPair using (_,_)
open import Identity using (_≡_; refl; inv)
open import Identity.Reasoning

module Nat.Divides where

one-divides-any : ∀ n -> 1 divides n
one-divides-any n = n , Mul.left-unit n

any-divides-zero : ∀ n -> n divides 0
any-divides-zero n = 0 , refl

reflex : ∀ n -> n divides n
reflex n = 1 , refl

divides-x-y-then-x+y : ∀ d x y
  -> d divides x
  -> d divides y
  -> d divides (x + y)
divides-x-y-then-x+y d x y (k1 , d*k1≡x) (k2 , d*k2≡y)
  rewrite (inv d*k1≡x) | (inv d*k2≡y) = (k1 + k2) , Mul.distrib-+-left d k1 k2

{-
  Exercise 7.1

  d * k1 = x
  d * k2 = x + y
    => d * k2 = d * k1 + y
    => dist (d * k2) (d * k1) = y
    => d * dist k2 k1 = y
-}
divides-x-x+y-then-y : ∀ d x y
  -> d divides x
  -> d divides (x + y)
  -> d divides y
divides-x-x+y-then-y d x y (k1 , d*k1≡x) (k2 , d*k2≡x+y)
  rewrite (inv d*k1≡x) = dist k2 k1 , d*k3≡y where
    d*k3≡y : d * dist k2 k1 ≡ y
    d*k3≡y =
      begin
        d * dist k2 k1
      ≡⟨ inv (Dist.linear d k2 k1) ⟩
        dist (d * k2) (d * k1)
      ≡⟨ Dist.clear-add-eq (d * k2) (d * k1) y d*k2≡x+y ⟩
        y
      ∎

divides-y-x+y-then-y : ∀ d x y
  -> d divides y
  -> d divides (x + y)
  -> d divides x
divides-y-x+y-then-y d x y
  rewrite Add.commutative x y = divides-x-x+y-then-y d y x
