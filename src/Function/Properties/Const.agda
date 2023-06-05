open import Type using (Type)
open import Function using (const; _∘_)
open import Function.Extensionality using (∀-extensionality)
open import Identity using (_≡_)
open import Identity.Reasoning

module Function.Properties.Const where

{-
  Exercise 2.3.b
  Ctx |- f : A -> B
  -------------------------------------------
  Ctx, z : C |- const_z ∘ f = const_z : A -> C
-}
const-comp-right : {A B C : Type}
  -> (f : A -> B)
  -> (z : C) -> (const z) ∘ f ≡ const z
const-comp-right f z = ∀-extensionality λ x -> 
  begin
    (const z ∘ f) x
  ≡⟨⟩
    const z (f x)
  ≡⟨⟩
    z
  ≡⟨⟩
    const z x
  ∎

{-
  Exercise 2.3.c
  Ctx |- A type
  Ctx |- g : B -> C
  --------------------
  Ctx, y : B |- g ∘ const_y = const_{g y} : A -> C
-}
comp-left : {B C : Type}
  -> (A : Type)
  -> (g : B -> C)
  -> (y : B) -> (g ∘ const y) ≡ const (g y)
comp-left A g y = ∀-extensionality λ (x : A) -> 
  begin
    (g ∘ const y) x
  ≡⟨⟩
    g (const y x)
  ≡⟨⟩
    g y
  ≡⟨⟩
    const (g y) x
  ∎