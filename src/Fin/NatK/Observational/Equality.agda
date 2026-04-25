import Fin.Observational.Equality as FinEq

open import Fin.Base
open import Fin.NatK.Base
open import DependentPair
open import Identity

module Fin.NatK.Observational.Equality where

reflex : ∀ {k} -> (n : ℕ k) -> Eq-ℕ n n
reflex (constant x) = FinEq.reflex x
reflex (unary x n) = FinEq.reflex x , reflex n

eq-identity-fwd : ∀ {k} -> (n m : ℕ k) -> n ≡ m -> Eq-ℕ n m
eq-identity-fwd n _ refl = reflex n

eq-identity-bck : ∀ {k} -> (n m : ℕ k) -> Eq-ℕ n m -> n ≡ m 
eq-identity-bck (constant x) (constant y) eq 
  rewrite FinEq.eq-identity-bck x y eq = refl
eq-identity-bck (unary x n) (unary y m) (eqFin , eqℕ)
  rewrite FinEq.eq-identity-bck x y eqFin 
  | eq-identity-bck n m eqℕ = refl

eq-identity : ∀ {k} -> (n m : ℕ k) -> (n ≡ m) <--> Eq-ℕ n m
eq-identity n m = eq-identity-fwd n m , eq-identity-bck n m

constant≢unary : ∀ {k} -> (x y : Fin k) -> (n : ℕ k) -> constant x ≢ unary y n
constant≢unary x y n = eq-identity-fwd (constant x) (unary y n)
