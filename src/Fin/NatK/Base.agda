open import Fin.Base
open import Nat.Base
open import Type
open import Empty
open import Empty.Negation
open import DependentPair

module Fin.NatK.Base where

data ℕ : Nat -> Type where
  constant : ∀ {k} -> Fin k -> ℕ k
  unary : ∀ {k} -> Fin k -> ℕ k -> ℕ k

to-nat : ∀ {k} -> ℕ k -> Nat
to-nat (constant x) = incl x
to-nat {k} (unary x n) = k * (to-nat n + 1) + incl x

{-
  Exercise 7.10.a
-}
empty-ℕ₀ : is-empty (ℕ 0)
empty-ℕ₀ (constant ())
empty-ℕ₀ (unary () _)

-- Observational Equality
Eq-ℕ : ∀ {k} -> ℕ k -> ℕ k -> Type
Eq-ℕ (constant x) (constant y) = Eq-Fin x y
Eq-ℕ (constant _) (unary _ _) = Empty
Eq-ℕ (unary _ _) (constant _) = Empty
Eq-ℕ (unary x n) (unary y m) = (Eq-Fin x y)  × (Eq-ℕ n m)
