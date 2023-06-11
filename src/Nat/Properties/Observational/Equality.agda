open import Type using (Type)
open import Nat using (Nat; zero; suc)
open import Unit using (Unit; unit)
open import Empty using (Empty)
open import Function using (_$_; _∘_)
open import DependentPair using (_<-->_; _,_; fst; snd)
open import Identity using (_≡_; _≢_; refl; ap)

module Nat.Properties.Observational.Equality where

Eq-Nat : Nat -> Nat -> Type
Eq-Nat zero zero = Unit
Eq-Nat zero (suc m) = Empty
Eq-Nat (suc n) zero = Empty
Eq-Nat (suc n) (suc m) = Eq-Nat n m

refl-Eq-Nat : (n : Nat) -> Eq-Nat n n
refl-Eq-Nat zero = unit
refl-Eq-Nat (suc n) = refl-Eq-Nat n

equiv-Eq-Nat-l : ∀ n m -> n ≡ m -> Eq-Nat n m
equiv-Eq-Nat-l n _ refl = refl-Eq-Nat n

equiv-Eq-Nat-r : ∀ n m ->  Eq-Nat n m -> n ≡ m
equiv-Eq-Nat-r zero zero _ = refl
equiv-Eq-Nat-r (suc n) (suc m) eqnat = ap suc (equiv-Eq-Nat-r n m eqnat)

equiv-Eq-Nat : ∀ n m -> (n ≡ m) <--> Eq-Nat n m
equiv-Eq-Nat n m = equiv-Eq-Nat-l n m , equiv-Eq-Nat-r n m

peano7-l : ∀ {n m} -> n ≡ m -> suc n ≡ suc m
peano7-l = ap suc

peano7-r : ∀ {n m} -> suc n ≡ suc m -> n ≡ m
peano7-r {n} {m} eq = snd (equiv-Eq-Nat n m) nEqm where
  nEqm : Eq-Nat n m
  nEqm = fst (equiv-Eq-Nat (suc n) (suc m)) eq

peano7 : ∀ {n m} -> (n ≡ m) <--> (suc n ≡ suc m)
peano7 =  peano7-l , peano7-r

peano8 : ∀ {n} -> zero ≢ suc n
peano8 {n} = equiv-Eq-Nat-l zero (suc n)

diff-from-suc : ∀ {n} -> n ≢ suc n
diff-from-suc {zero} = peano8
diff-from-suc {suc n} = diff-from-suc ∘ peano7-r
