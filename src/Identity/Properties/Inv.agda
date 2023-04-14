open import Identity using (_≡_; refl; refl-of; inv)

module Identity.Properties.Inv where

Type = Set

inv-unit : {A : Type} 
  -> (x : A)
  -> inv (refl-of x) ≡ refl-of x
inv-unit _ = refl