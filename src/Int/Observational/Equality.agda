import Nat
open import Nat.Observational.Equality using (Eq-Nat; refl-Eq-Nat; equiv-Eq-Nat-r)
open import Int.Base
open import Type using (Type)
open import Unit using (Unit; unit)
open import Empty using (Empty; ex-falso)
open import Function using (id; _∘_)
open import DependentPair using (_<-->_; _,_)
open import Identity using (_≢_; _≡_; refl; ap)

module Int.Observational.Equality where

Eq-Int : Int -> Int -> Type
Eq-Int (in-neg x) (in-neg y) = Eq-Nat x y
Eq-Int (in-neg x) zero = Empty
Eq-Int (in-neg x) (in-pos y) = Empty
Eq-Int zero (in-neg y) = Empty
Eq-Int zero zero = Unit
Eq-Int zero (in-pos y) = Empty
Eq-Int (in-pos x) (in-neg y) = Empty
Eq-Int (in-pos x) zero = Empty
Eq-Int (in-pos x) (in-pos y) = Eq-Nat x y

refl-Eq-Int : ∀ x -> Eq-Int x x
refl-Eq-Int (in-neg Nat.zero) = unit
refl-Eq-Int (in-neg (Nat.suc x)) = refl-Eq-Nat x
refl-Eq-Int zero = unit
refl-Eq-Int (in-pos Nat.zero) = unit
refl-Eq-Int (in-pos (Nat.suc x)) = refl-Eq-Nat x

equiv-Eq-Int-fwd : ∀ x y -> x ≡ y -> Eq-Int x y
equiv-Eq-Int-fwd x _ refl = refl-Eq-Int x

equiv-Eq-Int-bck : ∀ x y -> Eq-Int x y -> x ≡ y
equiv-Eq-Int-bck (in-neg x) (in-neg y) = ap in-neg ∘ equiv-Eq-Nat-bck x y
equiv-Eq-Int-bck zero zero _ = refl
equiv-Eq-Int-bck (in-pos x) (in-pos y) = ap in-pos ∘ equiv-Eq-Nat-bck x y

equiv-Eq-Nat : ∀ x y -> (x ≡ y) <--> (Eq-Int x y)
equiv-Eq-Nat x y = equiv-Eq-Int-fwd x y , equiv-Eq-Int-bck x y

not-zero-pos : ∀ {m} -> zero ≢ in-pos m
not-zero-pos {m} = equiv-Eq-Int-fwd zero (in-pos m)

not-zero-neg : ∀ {m} -> zero ≢ in-neg m
not-zero-neg {m} = equiv-Eq-Int-fwd zero (in-neg m)
