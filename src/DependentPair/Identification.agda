open import DependentPair.Base
open import Identity.Base using (_≡_; refl; tr)
open import Type using (Type)

module DependentPair.Identification where

eq-fst : {A : Type} {B : A -> Type}
  -> (x1 x2 : A)
  -> (y1 : B x1) -> (y2 : B x2)
  -> fst {A} {B} (x1 , y1) ≡ fst {A} {B} (x2 , y2)
  -> x1 ≡ x2
eq-fst _ _ _ _ refl = refl

eq-both-fwd : {A B : Type} {a1 a2 : A} {b1 b2 : B}
  -> a1 ≡ a2
  -> b1 ≡ b2
  -> (a1 , b1) ≡ (a2 , b2)
eq-both-fwd refl refl = refl

eq-both-bck : {A B : Type} {a1 a2 : A} {b1 b2 : B}
  -> (a1 , b1) ≡ (a2 , b2)
  -> (a1 ≡ a2) × (b1 ≡ b2)
eq-both-bck refl = refl , refl

{-
  Note that for the type (eq : a1 ≡ a2) -> tr eq b1 ≡ b2 -> (a1 , b1) ≡ (a2 , b2)

  When we pattern match on eq with (refl {a1}), we get:

  id b1 ≡ b2 -> (a1 , id b1) -> (a1 , b2)

  Then when we pattern match with (refl {id b1}) we end up with

  (a1 , b2) ≡ (a1 , b2)
-}
eq-both-dep-fwd : {A : Type} {B : A -> Type}
  -> (a1 : A) (b1 : B a1)
  -> (a2 : A) (b2 : B a2)
  -> (eq : a1 ≡ a2)
  -> tr eq b1 ≡ b2
  -> (a1 , b1) ≡ (a2 , b2)
eq-both-dep-fwd a1 b1 a2 b2 refl refl = refl

eq-both-dep-bck-snd : {A : Type} {B : A -> Type}
  -> (a1 : A) (b1 : B a1)
  -> (a2 : A) (b2 : B a2)
  -> (eq : a1 ≡ a2)
  -> (a1 , b1) ≡ (a2 , b2)
  -> tr eq b1 ≡ b2
eq-both-dep-bck-snd a1 b1 a2 b2 refl refl = refl

eq-both-dep-bck-fst : {A : Type} {B : A -> Type}
  -> (a1 : A) (b1 : B a1)
  -> (a2 : A) (b2 : B a2)
  -> (a1 , b1) ≡ (a2 , b2)
  -> a1 ≡ a2
eq-both-dep-bck-fst a1 b1 a2 b2 refl = refl
