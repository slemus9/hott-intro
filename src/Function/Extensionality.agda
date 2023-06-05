open import Type using (Type)
open import Identity using (_≡_)

module Function.Extensionality where

{-
  TODO: Is there a better representation?
-}
postulate
  ∀-extensionality : {A : Type} {B : A -> Type} {f g : (x : A) -> B x}
    -> (∀ x -> f x ≡ g x)
    -> f ≡ g

extensionality : {A B : Type} {f g : A -> B}
    -> (∀ x -> f x ≡ g x)
    -> f ≡ g
extensionality {A} {B} = ∀-extensionality {A} {λ _ -> B}