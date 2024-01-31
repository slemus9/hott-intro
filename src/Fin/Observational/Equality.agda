open import DependentPair using (_<-->_; _,_)
open import Empty using (ex-falso)
open import Fin.Base
open import Function using (_∘_; _$_)
open import Identity using (_≢_; _≡_; refl; ap; sym)
open import Unit using (unit)


module Fin.Observational.Equality where

reflex : ∀ {k} -> (x : Fin k) -> Eq-Fin x x
reflex base = unit
reflex (i x) = reflex x

{-
  Exercise 7.5.a
-}
eq-identity-fwd : ∀ {k} -> (x y : Fin k) -> x ≡ y -> Eq-Fin x y
eq-identity-fwd x _ refl = reflex x

eq-identity-bck : ∀ {k} -> (x y : Fin k) -> Eq-Fin x y -> x ≡ y
eq-identity-bck base base _ = refl
eq-identity-bck (i x) (i y) eq = ap i (eq-identity-bck x y eq)

eq-identity : ∀ {k} -> (x y : Fin k) -> (x ≡ y) <--> Eq-Fin x y
eq-identity x y = eq-identity-fwd x y , eq-identity-bck x y

{-
  Exercise 7.5.b
-}
i-injective : ∀ {k} -> (x y : Fin k) -> i x ≡ i y -> x ≡ y
i-injective x y = eq-identity-bck x y ∘ eq-identity-fwd (i x) (i y)

{-
  Exercise 7.5.c
-}
zero≢next : ∀ {k} -> (x : Fin k) -> first ≢ next (i x)
zero≢next base = eq-identity-fwd (i first) base
zero≢next (i x) = zero≢next x ∘ i-injective first (next $ i x)

to-next-fin-injective : ∀ {k} -> (x y : Fin k) -> to-next-fin x ≡ to-next-fin y -> x ≡ y
to-next-fin-injective base base _ = refl
to-next-fin-injective base (i y) = ex-falso ∘ eq-identity-fwd base (i $ to-next-fin y)
to-next-fin-injective (i x) base = ex-falso ∘ eq-identity-fwd (i $ to-next-fin x) base
to-next-fin-injective (i x) (i y) eq = ap i $ to-next-fin-injective x y fx≡fy where
  fx-Eq-fy : Eq-Fin (to-next-fin x) (to-next-fin y)
  fx-Eq-fy = eq-identity-fwd (i $ to-next-fin x) (i $ to-next-fin y) eq

  fx≡fy : to-next-fin x ≡ to-next-fin y
  fx≡fy = eq-identity-bck (to-next-fin x) (to-next-fin y) fx-Eq-fy

{-
  Exercise 7.5.d
-}
next-injective : ∀ {k} -> (x y : Fin k) -> next x ≡ next y -> x ≡ y
next-injective base base _ = refl
next-injective base (i y) = ex-falso ∘ zero≢next y
next-injective (i x) base = ex-falso ∘ zero≢next x ∘ sym
next-injective (i x) (i y) = ap i ∘ to-next-fin-injective x y
