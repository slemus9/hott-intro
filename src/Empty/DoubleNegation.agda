open import Type using (Type)
open import Empty using (¬_)
open import Function using (_∘_)

module Empty.DoubleNegation where

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
