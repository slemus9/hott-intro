open import Type
open import Nat.Base
open import DependentPair.Base
open import Identity.Base
open import Decidable.Base
open import Empty.Negation.Base
open import Function.Base

import Nat.Divides as Divides
import Nat.WellOrdering as WellOrdering
import Nat.Leq as Leq

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

{-
  Type family that we will use to define the Greatest Common Divisor in terms of the Well-Ordering Principle
-}
well-ordered-gcd : Nat -> Nat -> Nat -> Type 
well-ordered-gcd a b n = 
  a + b ≢ 0 -> (n ≢ 0) × (∀ x -> (x divides a) × (x divides b) -> x divides n)

{-
  In order to use the Well-Ordering Principle, we first need to show that the give type family is decidable
-}
well-ordered-gcd-is-decidable : ∀ a b -> decidable-family (well-ordered-gcd a b)
well-ordered-gcd-is-decidable a b n = 
  to-decidable-function sum-not-zero common-div where
    sum-not-zero : decidable (a + b ≢ 0)
    sum-not-zero = neg (eq-nat (a + b) 0)

    n-not-zero : decidable (n ≢ 0)
    n-not-zero = neg (eq-nat n 0)

    common-div-pre : decidable-family (λ x -> (x divides a) × (x divides b))
    common-div-pre x = product (divides-nat x a) (divides-nat x b)

    common-div-post : decidable-family (λ x -> x divides n)
    common-div-post x = divides-nat x n

    upper : (a + b ≢ 0) -> is-upper-bound (λ x -> (x divides a) × (x divides b)) (a + b)
    upper not-zero x (div-a , div-b) = 
      Divides.addition-to-upper-bound a b x not-zero div-a div-b

    common-div : (a + b ≢ 0) -> decidable ((n ≢ 0) × (∀ x -> (x divides a) × (x divides b) -> x divides n))
    common-div not-zero = 
      product n-not-zero (function-nat-families (a + b) common-div-pre common-div-post (upper not-zero))

{-
  We also need to show that there is an element of the type family in order to use Well-Ordering Principle
-}
sum-is-well-ordered-gcd : ∀ a b -> well-ordered-gcd a b (a + b)
sum-is-well-ordered-gcd a b not-zero = 
  (not-zero , divides-sum) where
    divides-sum : ∀ x -> (x divides a) × (x divides b) -> x divides (a + b)
    divides-sum x (div-a , div-b) = Divides.divides-x-y-then-x+y x a b div-a div-b

-- Apply and open the WellOrdering module for the well-ordered-gcd type family
open module GcdWellOrdering (a b : Nat) = 
  WellOrdering (well-ordered-gcd a b) (well-ordered-gcd-is-decidable a b)

{-
  Definition of Greatest Common Divisor in terms of the Well Ordering Principle
-}
gcd : (a b : Nat) -> Σ Nat (λ n -> (well-ordered-gcd a b n) × is-lower-bound (well-ordered-gcd a b) n) 
gcd a b = 
  well-ordering a b ((a + b) , sum-is-well-ordered-gcd a b)

when-gcd-zero-fwd : (a b n : Nat) 
  -> well-ordered-gcd a b n
  -> n ≡ 0
  -> a + b ≡ 0
when-gcd-zero-fwd a b n wo-gcd n-is-zero = 
  double-neg (eq-nat (a + b) 0) not-not-zero where
    not-not-zero : ¬ (a + b ≢ 0)
    not-not-zero not-zero = fst (wo-gcd not-zero) n-is-zero

when-gcd-zero-bck : (a b n : Nat)
  -> is-lower-bound (well-ordered-gcd a b) n
  -> a + b ≡ 0
  -> n ≡ 0
when-gcd-zero-bck a b n low-bound sum-is-zero = 
  Leq.when-n≤0 (n-leq-zero sum-is-zero n-leq-sum) where
    n-leq-sum : n ≤ a + b
    n-leq-sum = low-bound (a + b) (sum-is-well-ordered-gcd a b)

    n-leq-zero : a + b ≡ 0 -> n ≤ a + b -> n ≤ 0
    n-leq-zero eq rewrite eq = id

when-gcd-zero : (a b n : Nat)
  -> well-ordered-gcd a b n
  -> is-lower-bound (well-ordered-gcd a b) n
  -> (n ≡ 0) <--> (a + b ≡ 0)
when-gcd-zero a b n wo-gcd low-bound = 
  when-gcd-zero-fwd a b n wo-gcd , when-gcd-zero-bck a b n low-bound

when-gcd-zero-uncurry : (a b : Nat) -> (fst (gcd a b) ≡ 0) <--> ((a + b) ≡ 0)
when-gcd-zero-uncurry a b with gcd a b
... | n , (wo-gcd , low-bound) = when-gcd-zero a b n wo-gcd low-bound
