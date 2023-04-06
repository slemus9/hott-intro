open import Identity.Def using (_≡_; refl)

module Function.Properties.Function where

Type = Set

func-η : {A B : Type} 
  -> (f : A -> B)
  -> (λ x -> f x) ≡ f
func-η _ = refl