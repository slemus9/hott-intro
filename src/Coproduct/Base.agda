open import Type using (Type)
open import Empty.Base using (ex-falso)
open import Empty.Negation.Base using (is-empty)

module Coproduct.Base where

-- Coproduct or Disjoint Sum
data _⨄_ (A B : Type) : Type where
  inl : A -> A ⨄ B
  inr : B -> A ⨄ B

----------------
-- Operations --
----------------

{-
  Induction principle:
  Ctx, x : A ⨄ B |- P x type
      Ctx, a : A |- l : P (inl a)
      Ctx, b : B |- r : P (inr b)
  ---------------------------------------------------
  Ctx, x : A ⨄ B |- ind(l, r, x) : (x : A ⨄ B) -> P x

  Computation rules:
  Ctx, x : A ⨄ B |- P x type
      Ctx, a : A |- l : P (inl a)
      Ctx, b : B |- r : P (inr b)
  ---------------------------------
  Ctx, a : A     |- ind(l, r, inl a) : P (inl a)

  Ctx, x : A ⨄ B |- P x type
      Ctx, a : A |- l : P (inl a)
      Ctx, b : B |- r : P (inr b)
  ---------------------------------
  Ctx, b : B     |- ind(l, r, inr b) : P (inr b)
-}
ind-coprod : {A B : Type} {P : A ⨄ B -> Type}
  -> (∀ a -> P (inl a))
  -> (∀ b -> P (inr b))
  -> ∀ x -> P x
ind-coprod f _ (inl a) = f a
ind-coprod _ g (inr b) = g b

fold-coprod : {A B C : Type}
  -> (A -> C)
  -> (B -> C)
  -> A ⨄ B -> C
fold-coprod = ind-coprod

function-sum : {A B C D : Type}
  -> (A -> C)
  -> (B -> D)
  -> A ⨄ B -> C ⨄ D
function-sum f _ (inl a) = inl (f a)
function-sum _ g (inr b) = inr (g b)

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
