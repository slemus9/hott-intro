open import Type using (Type)
open import Nat.Base using (Nat; zero; suc)
open import Unit using (Unit; unit)
open import Empty using (Empty)
open import Function using (_$_; _∘_)
open import DependentPair using (_<-->_; _,_; fst; snd)
open import Identity using (_≡_; _≢_; refl; ap)

module Nat.Observational.Equality where

Eq-Nat : Nat -> Nat -> Type
Eq-Nat zero zero = Unit
Eq-Nat zero (suc m) = Empty
Eq-Nat (suc n) zero = Empty
Eq-Nat (suc n) (suc m) = Eq-Nat n m

refl-Eq-Nat : (n : Nat) -> Eq-Nat n n
refl-Eq-Nat zero = unit
refl-Eq-Nat (suc n) = refl-Eq-Nat n

equiv-Eq-Nat-fwd : ∀ n m -> n ≡ m -> Eq-Nat n m
equiv-Eq-Nat-fwd n _ refl = refl-Eq-Nat n

equiv-Eq-Nat-bck : ∀ n m -> Eq-Nat n m -> n ≡ m
equiv-Eq-Nat-bck zero zero _ = refl
equiv-Eq-Nat-bck (suc n) (suc m) eqnat = ap suc (equiv-Eq-Nat-bck n m eqnat)

equiv-Eq-Nat : ∀ n m -> (n ≡ m) <--> Eq-Nat n m
equiv-Eq-Nat n m = equiv-Eq-Nat-fwd n m , equiv-Eq-Nat-bck n m

peano7-fwd : ∀ {n m} -> n ≡ m -> suc n ≡ suc m
peano7-fwd = ap suc

peano7-bck : ∀ {n m} -> suc n ≡ suc m -> n ≡ m
peano7-bck {n} {m} eq = snd (equiv-Eq-Nat n m) nEqm where
  nEqm : Eq-Nat n m
  nEqm = fst (equiv-Eq-Nat (suc n) (suc m)) eq

peano7 : ∀ {n m} -> (n ≡ m) <--> (suc n ≡ suc m)
peano7 =  peano7-fwd , peano7-bck

peano8 : ∀ {n} -> zero ≢ suc n
peano8 {n} = equiv-Eq-Nat-fwd zero (suc n)

diff-from-suc : ∀ {n} -> n ≢ suc n
diff-from-suc {zero} = peano8
diff-from-suc {suc n} = diff-from-suc ∘ peano7-bck
