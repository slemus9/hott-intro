open import Function using (_∘_)
open import Empty using (¬_; ex-falso)
open import DependentPair using (_×_; pair)
open import Coproduct using (_⨄_; inl; inr)

module DoubleNegation where

  Type = Set

  {-
    Exercise 4.3.b
    Double negation monad
  -}
  pure : {P : Type}
    -> P -> ¬ ¬ P
  pure p notP = notP p

  _>>=_ : {P Q : Type}
    -> ¬ ¬ P -> (P -> ¬ ¬ Q) -> ¬ ¬ Q
  (dnP >>= f) notQ = dnP (λ p -> f p notQ)

  map : {P Q : Type}
    -> (P -> Q) -> ¬ ¬ P -> ¬ ¬ Q
  map f dnP = dnP >>= (pure ∘ f)

  _=<<_ : {P Q : Type}
    -> (P -> ¬ ¬ Q) -> ¬ ¬ P -> ¬ ¬ Q
  f =<< dnP = dnP >>= f

  {-
    Exercise 4.3.c
    Some classical laws with double negation
  -}
  classic1 : {P : Type}
    -> ¬ ¬ (¬ ¬ P -> P)
  classic1 notImpl = notImpl λ dnP -> ex-falso (dnP λ p -> notImpl λ _ -> p)

  classic2 : {P Q : Type}
    -> ¬ ¬ (((P -> Q) -> P) -> P)
  classic2 notImpl = notImpl λ f -> f λ p -> ex-falso (notImpl λ _ -> p)

  classic3 : {P Q : Type}
    -> ¬ ¬ ((P -> Q) ⨄ (Q -> P))
  classic3 notPlus = notPlus (inl λ p -> ex-falso (notPlus (inr λ _ -> p)))

  classic4 : {P : Type}
    -> ¬ ¬ (P ⨄ (¬ P))
  classic4 notEM = notEM (inr λ p -> notEM (inl p))
