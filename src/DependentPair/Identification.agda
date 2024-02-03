open import DependentPair
open import Identity using (_≡_; refl)
open import Type using (Type)

module DependentPair.Identification where

eq-fst : {A : Type} {B : A -> Type}
  -> (x1 x2 : A)
  -> (y1 : B x1) -> (y2 : B x2)
  -> fst {A} {B} (x1 , y1) ≡ fst {A} {B} (x2 , y2)
  -> x1 ≡ x2
eq-fst _ _ _ _ refl = refl
