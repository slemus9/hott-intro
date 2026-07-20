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
