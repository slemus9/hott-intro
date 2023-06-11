open import Type using (Type)
open import Unit using (Unit; unit)
open import Empty using (Empty)
open import Bool using (Bool; true; false; neg)
open import DependentPair using (_<-->_; _,_)
open import Identity using (_≢_; _≡_; refl)

module Bool.Properties.Observational.Equality where

{-
  Exercise 6.2.a
-}
Eq-Bool : Bool -> Bool -> Type
Eq-Bool true true = Unit
Eq-Bool false false = Unit
Eq-Bool _ _ = Empty

{-
  Exercise 6.2.b
-}
refl-Eq-Bool : ∀ b -> Eq-Bool b b
refl-Eq-Bool true = unit
refl-Eq-Bool false = unit

equiv-Eq-Bool-l : ∀ a b -> a ≡ b -> Eq-Bool a b
equiv-Eq-Bool-l a _ refl = refl-Eq-Bool a

equiv-Eq-Bool-r : ∀ a b -> Eq-Bool a b -> a ≡ b
equiv-Eq-Bool-r true true unit = refl
equiv-Eq-Bool-r false false unit = refl

equiv-Eq-Bool : ∀ a b -> (a ≡ b) <--> Eq-Bool a b
equiv-Eq-Bool a b = equiv-Eq-Bool-l a b , equiv-Eq-Bool-r a b

{-
  Exercise 6.2.c
-}
ineq-neg : ∀ b -> b ≢ neg b
ineq-neg true = equiv-Eq-Bool-l true false
ineq-neg false = equiv-Eq-Bool-l false true

false-not-true : false ≢ true
false-not-true = ineq-neg false
