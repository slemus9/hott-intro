open import Function using (swap; id; _∘_)
open import Function.Extensionality using (∀-extensionality)
open import Identity using (_≡_)
open import Identity.Reasoning

module Function.Properties.Swap where

Type = Set

{-
  Exercise 2.4.b
  Ctx |- A type
  Ctx |- B type
  Ctx, x : A, y: B |- (C x y) type
  ----------------------------------------------------------------------------------------
  Ctx |- swap ∘ swap = id : ((x : A) -> (y : B) -> C x y) -> ((y : B) -> (x : A) -> C x y)
-}
swap-comp-is-id : (A B : Type) (C : A -> B -> Type)
  -> swap ∘ swap ≡ id
swap-comp-is-id A B C = 
  ∀-extensionality λ (f : ∀ x -> ∀ y -> C x y) -> 
    ∀-extensionality λ x -> 
      ∀-extensionality λ y -> 
        begin
          (swap ∘ swap) f x y
        ≡⟨⟩
          (swap (swap f)) x y
        ≡⟨⟩
          (λ (x1 : A) -> λ (y1 : B) -> swap f y1 x1) x y
        ≡⟨⟩
          (λ y1 -> swap f y1 x) y
        ≡⟨⟩
          swap f y x
        ≡⟨⟩
          f x y
        ≡⟨⟩
          (id f) x y
        ∎