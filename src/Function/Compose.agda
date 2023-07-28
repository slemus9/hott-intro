open import Type using (Type)
open import Function.Base using (id; _∘_)
open import Function.Extensionality using (extensionality)
open import Identity.Base using (_≡_; refl)
open import Identity.Reasoning

module Function.Compose where

{-
  Ctx |- f : A -> B
  ---------------------
  Ctx |- id ∘ f = f : A -> B
-}
left-unit : {A B : Type}
  -> (f : A -> B)
  -> (id ∘ f) ≡ f
left-unit f = extensionality λ x ->
  begin
    (id ∘ f) x
  ≡⟨⟩
    id (f x)
  ≡⟨⟩
    f x
  ∎

{-
  Exercise 2.2
  Ctx |- f : A -> B
  ---------------------
  Ctx |- f ∘ id = f : A -> B
-}
right-unit : {A B : Type}
  -> (f : A -> B)
  -> (f ∘ id) ≡ f
right-unit f = extensionality λ _ → refl
