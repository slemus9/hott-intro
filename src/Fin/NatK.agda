open import Fin.Base
import Fin.Observational.Equality as FinEq
import Fin.Incl as Incl
open import Nat.Base
import Nat.Less as Less
import Nat.Add as Add
open import Type
open import Identity
open import Empty.Negation
open import Empty
open import DependentPair
open import Function

module Fin.NatK where

data ℕₖ : Nat -> Type where
  constant : ∀ {k} -> Fin k -> ℕₖ k
  unary : ∀ {k} -> Fin k -> ℕₖ k -> ℕₖ k

to-nat : ∀ {k} -> ℕₖ k -> Nat
to-nat (constant x) = incl x
to-nat {k} (unary x n) = k * (to-nat n + 1) + incl x

{-
  Exercise 7.10.a
-}
empty-ℕ₀ : is-empty (ℕₖ 0)
empty-ℕ₀ (constant ())
empty-ℕ₀ (unary () _)

-- Observational Equality
Eq-ℕₖ : ∀ {k} -> ℕₖ k -> ℕₖ k -> Type
Eq-ℕₖ (constant x) (constant y) = Eq-Fin x y
Eq-ℕₖ (constant _) (unary _ _) = Empty
Eq-ℕₖ (unary _ _) (constant _) = Empty
Eq-ℕₖ (unary x n) (unary y m) = (Eq-Fin x y)  × (Eq-ℕₖ n m)

module Observational where

  reflex : ∀ {k} -> (n : ℕₖ k) -> Eq-ℕₖ n n
  reflex (constant x) = FinEq.reflex x
  reflex (unary x n) = FinEq.reflex x , reflex n

  eq-identity-fwd : ∀ {k} -> (n m : ℕₖ k) -> n ≡ m -> Eq-ℕₖ n m
  eq-identity-fwd n _ refl = reflex n

  eq-identity-bck : ∀ {k} -> (n m : ℕₖ k) -> Eq-ℕₖ n m -> n ≡ m 
  
  eq-identity-bck (constant x) (constant y) eq 
    rewrite FinEq.eq-identity-bck x y eq = refl

  eq-identity-bck (unary x n) (unary y m) (eqFin , eqℕₖ)
    rewrite FinEq.eq-identity-bck x y eqFin 
    | eq-identity-bck n m eqℕₖ = refl

  eq-identity : ∀ {k} -> (n m : ℕₖ k) -> (n ≡ m) <--> Eq-ℕₖ n m
  eq-identity n m = eq-identity-fwd n m , eq-identity-bck n m

  constant≢unary : ∀ {k} -> (x y : Fin k) -> (n : ℕₖ k) -> constant x ≢ unary y n
  constant≢unary x y n = eq-identity-fwd (constant x) (unary y n)

to-nat-injective : ∀ {k} -> (n m : ℕₖ k) -> to-nat n ≡ to-nat m -> n ≡ m

to-nat-injective (constant x) (constant y) = ap constant ∘ Incl.injective

to-nat-injective {k} (constant x) (unary y m) eq
  rewrite Add.associative k (k * to-nat m) (incl y) = 
    ex-falso (Less.not-n+m<n contradiction) where
      contradiction : k + (k * to-nat m + incl y) < k
      contradiction = tr {Nat} {_< k} eq (Incl.bounded x)

to-nat-injective {k} (unary x n) (constant y) eq 
  rewrite Add.associative k (k * to-nat n) (incl x) = 
    ex-falso (Less.not-n+m<n contradiction) where
      contradiction : k + (k * to-nat n + incl x) < k
      contradiction = tr {Nat} {_< k} (sym eq) (Incl.bounded y)

to-nat-injective (unary x n) (unary y m) = {!   !}
