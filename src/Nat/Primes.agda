open import Nat.Base
open import Coproduct.Base
open import DependentPair.Base
open import Decidable.Base
open import Empty.Base
open import Empty.Negation.Base
open import Identity.Base
open import Function.Base
open import Type

import Nat.Divides as Divides
import Nat.Observational.Equality as NatEq
import Nat.Less as Less
import Nat.Factorial as Fact
import Nat.Mul as Mul

module Nat.Primes where

is-proper-divisor : Nat -> Nat -> Type
is-proper-divisor n d = (d ≢ n) × (d divides n)

is-prime : Nat -> Type
is-prime n = ∀ x -> (is-proper-divisor n x) <--> (x ≡ 1)

{-
  Alternative is-prime definition that can be easier to manipulate in some cases
-}
is-prime-aux : Nat -> Type
is-prime-aux n = (n ≢ 1) × (∀ x -> is-proper-divisor n x -> x ≡ 1)

is-prime-to-aux : ∀ n -> is-prime n -> is-prime-aux n
is-prime-to-aux n n-is-prime with eq-nat n 1 
... | inl is-one = ex-falso (fst (snd (n-is-prime n) is-one) refl) -- One is not a proper divisor of itself
... | inr is-not-one = is-not-one , λ x -> fst (n-is-prime x)

aux-to-is-prime : ∀ n -> is-prime-aux n -> is-prime n
aux-to-is-prime n (is-not-one , f) x = 
  forwards , backwards where
    forwards : is-proper-divisor n x -> x ≡ 1
    forwards = f x

    backwards : x ≡ 1 -> is-proper-divisor n x
    backwards refl = (is-not-one ∘ inv) , Divides.one-divides-any n

is-prime-iff-aux : ∀ n -> (is-prime n) <--> (is-prime-aux n)
is-prime-iff-aux n = is-prime-to-aux n , aux-to-is-prime n

{-
  Any non-zero natural number is a proper divisor of 0
-}
is-proper-divisor-of-zero : ∀ x -> is-proper-divisor 0 (suc x)
is-proper-divisor-of-zero x = (NatEq.peano8 ∘ sym) , Divides.any-divides-zero (suc x)

{-
  Zero is not a prime number
-}
not-zero-is-prime-aux : ¬ (is-prime-aux 0)
not-zero-is-prime-aux (_ , f) =
  NatEq.diff-from-suc (sym two-eq-one) where
    two-eq-one : 2 ≡ 1
    two-eq-one = f 2 (is-proper-divisor-of-zero 1)

is-proper-divisor-is-decidable : ∀ n d -> decidable (is-proper-divisor n d)
is-proper-divisor-is-decidable n d =
  product (neg (eq-nat d n)) (divides-nat d n)

{-
  is-prime-aux is a decidable type family
-}
is-prime-aux-is-decidable : decidable-family (is-prime-aux)
is-prime-aux-is-decidable zero = inr not-zero-is-prime-aux
is-prime-aux-is-decidable (suc n) =
  product fst-component snd-component where
    fst-component : decidable (suc n ≢ 1)
    fst-component = neg (eq-nat (suc n) 1)

    up : is-upper-bound (is-proper-divisor (suc n)) (suc n)
    up x (_ , div) = Divides.suc-upper-bound x n div

    snd-component : decidable (∀ x -> is-proper-divisor (suc n) x -> x ≡ 1)
    snd-component = 
      function-nat-families (suc n) (is-proper-divisor-is-decidable (suc n)) (λ x -> eq-nat x 1) up

{-
  is-prime is a decidable type family
-}
is-prime-is-decidable : decidable-family (is-prime)
is-prime-is-decidable n = from-bijection-bck (is-prime-iff-aux n) (is-prime-aux-is-decidable n)

relatively-prime : Nat -> Nat -> Type
relatively-prime n m = (n < m) × ∀ x -> x ≤ n -> x divides m -> x ≡ 1

{-
  relatively-prime is a decidable type family
-}
relatively-prime-is-decidable : ∀ n -> decidable-family (relatively-prime n)
relatively-prime-is-decidable n m = product fst-component snd-component where
  fst-component : decidable (n < m)
  fst-component = less-nat n m

  snd-component : decidable (∀ x -> x ≤ n -> x divides m -> x ≡ 1)
  snd-component = 
    function-nat-families n 
      (λ x -> leq-nat x n) 
      (λ x -> function (divides-nat x m) (eq-nat x 1)) 
      (λ _ -> id)

{-
  Proof that n is relatively prime to n! + 1
-}
factorial-relatively-prime : ∀ n -> relatively-prime n (n ! + 1)
factorial-relatively-prime n = fst-component , snd-component where 
  fst-component : n < n ! + 1
  fst-component = Less.from-leq (Fact.leq-than-factorial n)

  x-positive : ∀ x -> x divides (n ! + 1) -> x ≢ 0
  x-positive x (k , eq) = Less.when-not-zero-bck (Mul.when-product-positive {x} {k} {n ! + 1} 0<s eq)

  snd-component : ∀ x -> x ≤ n -> x divides (n ! + 1) -> x ≡ 1
  snd-component x leq div = 
    Divides.divides-consecutive x (n !)
      (Fact.all-leq-divide-factorial x n (x-positive x div) leq)
      div
