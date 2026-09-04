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
import Nat.Leq as Leq
import Nat.Factorial as Fact
import Nat.Mul as Mul
import Nat.WellOrdering as WellOrdering

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
zero-is-not-prime-aux : ¬ (is-prime-aux 0)
zero-is-not-prime-aux (_ , f) =
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
is-prime-aux-is-decidable zero = inr zero-is-not-prime-aux
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

{-
  Open the  WellOrdering module for the relatively-prime type family
-}
open module RelativelyPrimeWellOrdering (n : Nat) = 
  WellOrdering (relatively-prime n) (relatively-prime-is-decidable n)

{-
  Auxiliary module to prove that there are is is always a prime number greater than all non-zero natural numbers
-}
module InfinitelyMany 
  (n m : Nat)
  (0-less-n : 0 < n)
  (n-relatively-prime-m : relatively-prime n m)
  (low-bound : is-lower-bound (relatively-prime n) m) where

  private
    n-less-m : n < m
    n-less-m = fst n-relatively-prime-m

    f : ∀ x -> x ≤ n -> x divides m -> x ≡ 1
    f = snd n-relatively-prime-m

    m-greater-one : 1 < m
    m-greater-one = Less.trans-suc 0-less-n n-less-m

    m-positive : 0 < m
    m-positive = Less.trans 0<s m-greater-one

    m-not-one : m ≢ 1
    m-not-one = Less.not-eq m-greater-one ∘ inv

    m-only-proper-divisor-is-one : ∀ x -> is-proper-divisor m x -> x ≡ 1
    m-only-proper-divisor-is-one x (x-neq-m , (k , x-div-m)) = x-eq-one where
      x-leq-m : x ≤ m
      x-leq-m = Mul.mul-positive-ineq {x} {k} {m} m-positive x-div-m
      
      x-less-m : x < m
      x-less-m with Leq.to-less-or-equal x-leq-m
      -- when x ≡ m
      ... | inl x-eq-m = ex-falso (x-neq-m x-eq-m)
      -- when x < m
      ... | inr x-less-m = x-less-m

      x-not-relatively-prime-n : ¬ (relatively-prime n x)
      x-not-relatively-prime-n = neg-impl (Less.not-leq-fwd {x} {m} x-less-m) (low-bound x)

      x-proper-divisor : ∀ y -> y ≤ n -> y divides x -> y ≡ 1
      x-proper-divisor y y-leq-n y-div-x = f y y-leq-n (Divides.trans y x m y-div-x (k , x-div-m))

      not-n-less-x : ¬ (n < x)
      not-n-less-x = neg-and x-not-relatively-prime-n x-proper-divisor

      x-eq-one : x ≡ 1
      x-eq-one = f x (Less.not-less-to-leq not-n-less-x) (k , x-div-m)

  minimal-is-prime : (is-prime m) × (n < m)
  minimal-is-prime = aux-to-is-prime m (m-not-one , m-only-proper-divisor-is-one) , n-less-m


{-
  Proof that there are is is always a prime number greater than all non-zero natural numbers
-}
non-zero-infinitely-many : ∀ n -> 0 < n -> Σ Nat λ p -> is-prime p × (n < p)
non-zero-infinitely-many n 0-less-n with well-ordering n ((n ! + 1) , factorial-relatively-prime n)
... | (m , (n-relatively-prime-m , low-bound)) = 
  m , InfinitelyMany.minimal-is-prime n m 0-less-n n-relatively-prime-m low-bound

{-
  Proof that there are infinitely many primes
-}
infinitely-many : ∀ n -> Σ Nat λ p -> is-prime p × (n < p)
infinitely-many zero with non-zero-infinitely-many 1 0<s 
... | (p , (is-prime , leq)) = p , (is-prime , Less.trans 0<s leq)
infinitely-many (suc n) with non-zero-infinitely-many (suc n) 0<s 
... | (p , (is-prime , leq)) = p , (is-prime , leq)
