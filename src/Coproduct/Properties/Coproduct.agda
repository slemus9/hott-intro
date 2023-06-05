open import Type using (Type)
open import Coproduct using (_⨄_; inl; inr)
open import Empty using (is-empty; ex-falso)

module Coproduct.Properties.Coproduct where

-- Proposition 4.4.4
left-empty : {A B : Type}
  -> is-empty A
  -> A ⨄ B -> B
left-empty notA (inl a) = ex-falso (notA a)
left-empty _ (inr b) = b

right-empty : {A B : Type}
  -> is-empty B
  -> A ⨄ B -> A
right-empty _ (inl a) = a
right-empty notB (inr b) = ex-falso (notB b)
