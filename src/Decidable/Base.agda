open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (_<-->_; _×_; _,_; fst; snd)
open import Empty using (Empty; ex-falso)
open import Empty.Negation using (¬_)
open import Function using (_∘_; id)
open import Identity using (_≡_)
open import Nat using (Nat; zero; suc)
open import Nat.Observational.Equality using (Eq-Nat; equiv-Eq-Nat)
open import Type using (Type)
open import Unit using (Unit)

module Decidable.Base where

decidable : Type -> Type
decidable A = A ⨄ (¬ A)

has-decidable-eq : Type -> Type
has-decidable-eq A = (x y : A) -> decidable (x ≡ y)

unit : decidable Unit
unit = inl Unit.unit

empty : decidable Empty
empty = inr id

neg : {A : Type} -> decidable A -> decidable (¬ A)
neg (inl a) = inr λ ¬a -> ex-falso (¬a a)
neg (inr ¬a) = inl ¬a

coproduct : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A ⨄ B)
coproduct (inl a) _ = inl (inl a)
coproduct (inr _) (inl b) = inl (inr b)
coproduct (inr ¬a) (inr ¬b) = inr λ where
  (inl a) -> ¬a a
  (inr b) -> ¬b b

product : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A × B)
product (inl a) (inl b) = inl (a , b)
product (inl a) (inr ¬b) = inr (¬b ∘ snd)
product (inr ¬a) (inl b) = inr (¬a ∘ fst)
product (inr ¬a) (inr _) = inr (¬a ∘ fst)

function : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A -> B)
function _ (inl b) = inl λ _ -> b
function (inl a) (inr ¬b) = inr λ f -> ¬b (f a)
function (inr ¬a) (inr ¬b) = inl (ex-falso ∘ ¬a)

from-bijection-fwd : {A B : Type}
  -> A <--> B
  -> decidable A
  -> decidable B
from-bijection-fwd (f , _) (inl a) = inl (f a)
from-bijection-fwd (_ , g) (inr ¬a) = inr (¬a ∘ g)

from-bijection-bck : {A B : Type}
  -> A <--> B
  -> decidable B
  -> decidable A
from-bijection-bck (_ , g) (inl b) = inl (g b)
from-bijection-bck (f , _) (inr ¬b) = inr (¬b ∘ f)

if-bijection : {A B : Type}
  -> A <--> B
  -> decidable A <--> decidable B
if-bijection a<->b = from-bijection-fwd a<->b , from-bijection-bck a<->b

eq-nat : ∀ m n -> decidable (Eq-Nat m n)
eq-nat zero zero = unit
eq-nat zero (suc n) = empty
eq-nat (suc m) zero = empty
eq-nat (suc m) (suc n) = eq-nat m n

nat-has-eq : has-decidable-eq Nat
nat-has-eq m n = from-bijection-bck (equiv-Eq-Nat m n) (eq-nat m n)
