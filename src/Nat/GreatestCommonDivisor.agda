open import Type
open import Nat.Base
open import DependentPair.Base
open import Identity.Base

import Nat.Divides as Divides

module Nat.GreatestCommonDivisor where

is-gcd : (a b d : Nat) -> Type
is-gcd a b d = 
  ∀ x -> ((x divides a) × (x divides b)) <--> (x divides d)

gcd-divides-both : ∀ a b d
  -> is-gcd a b d
  -> (d divides a) × (d divides b)
gcd-divides-both a b d g = 
  snd (g d) (Divides.reflex d)

{-
  The property of being a greatest common divisor uniquely characterizes the greatest common divisor
-}
gcd-uniqueness : ∀ a b d d'
 -> is-gcd a b d
 -> is-gcd a b d'
 -> d ≡ d'
gcd-uniqueness a b d d' g g' = 
  Divides.antisym d d' d-div-d' d'-div-d where
    d-div-d' : d divides d'
    d-div-d' = fst (g' d) (gcd-divides-both a b d g)

    d'-div-d : d' divides d
    d'-div-d = fst (g d') (gcd-divides-both a b d' g')
