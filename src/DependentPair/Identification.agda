open import DependentPair.Base
open import Identity.Base using (_≡_; refl)
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
