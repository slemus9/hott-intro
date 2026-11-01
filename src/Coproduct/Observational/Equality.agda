open import Coproduct.Base
open import DependentPair.Base
open import Identity.Base
open import Empty.Base

open import Type

module Coproduct.Observational.Equality where

Eq-Copr : {A B : Type}
  -> A ⨄ B
  -> A ⨄ B
  -> Type
Eq-Copr (inl a1) (inl a2) = a1 ≡ a2
Eq-Copr (inr b1) (inr b2) = b1 ≡ b2
Eq-Copr _ _               = Empty

refl-Eq-Copr : {A B : Type} 
  -> (x : A ⨄ B)
  -> Eq-Copr x x
refl-Eq-Copr (inl a) = refl
refl-Eq-Copr (inr b) = refl

equiv-Eq-Copr-fwd : {A B : Type} {x y : A ⨄ B}
  -> x ≡ y
  -> Eq-Copr x y
equiv-Eq-Copr-fwd {_} {_} {x} {_} refl = refl-Eq-Copr x

equiv-Eq-Copr-bck : {A B : Type} {x y : A ⨄ B}
 -> Eq-Copr x y
 -> x ≡ y
equiv-Eq-Copr-bck {_} {_} {inl a1} {inl a2} = ap inl
equiv-Eq-Copr-bck {_} {_} {inr b1} {inr b2} = ap inr

{-
  Exercise 8.7.a
-}
equiv-Eq-Copr : {A B : Type} {x y : A ⨄ B}
  -> (x ≡ y) <--> (Eq-Copr x y)
equiv-Eq-Copr = equiv-Eq-Copr-fwd , equiv-Eq-Copr-bck
