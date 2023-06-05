open import Type using (Type)
open import Nat using (Nat; zero; suc)
open import Unit using (Unit; unit)
open import Empty using (Empty)
open import Function using (_<==>_; _iff_; _$_)
open import Identity using (_≡_; refl; ap)

module Nat.Properties.Observational.Equality where

Eq-Nat : Nat -> Nat -> Type
Eq-Nat zero zero = Unit
Eq-Nat zero (suc m) = Empty
Eq-Nat (suc n) zero = Empty
Eq-Nat (suc n) (suc m) = Eq-Nat n m

refl-Eq-Nat : (n : Nat) -> Eq-Nat n n
refl-Eq-Nat zero = unit
refl-Eq-Nat (suc n) = refl-Eq-Nat n

equiv-Eq-Nat : ∀ n m -> (n ≡ m) <==> Eq-Nat n m
equiv-Eq-Nat n m = to iff (from n m) where
  to : n ≡ m -> Eq-Nat n m
  to refl = refl-Eq-Nat n

  from : ∀ n m -> Eq-Nat n m -> n ≡ m
  from zero zero _ = refl
  from (suc n) (suc m) eqnat = ap suc (from n m eqnat)

peano7 : ∀ n m -> (n ≡ m) <==> (suc n ≡ suc m)
peano7 n m = to iff from where
  to : n ≡ m -> suc n ≡ suc m
  to = ap suc

  from : suc n ≡ suc m -> n ≡ m
  from eq = _<==>_.from (equiv-Eq-Nat n m) nEqm where
    nEqm : Eq-Nat n m
    nEqm = _<==>_.to (equiv-Eq-Nat (suc n) (suc m)) eq
