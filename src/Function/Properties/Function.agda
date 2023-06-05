open import Type using (Type)
open import Identity using (_≡_; refl)

module Function.Properties.Function where

func-η : {A B : Type} 
  -> (f : A -> B)
  -> (λ x -> f x) ≡ f
func-η _ = refl