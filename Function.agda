open import Equality using (_≡_; refl; cong; cong-app)
open Equality.≡-Reasoning

module Function where

Type = Set

postulate
  ∀-extensionality : {A : Type} {B : A -> Type} {f g : (x : A) -> B x}
    -> (∀ x -> f x ≡ g x)
    -> f ≡ g

extensionality : {A B : Type} {f g : A -> B}
    -> (∀ x -> f x ≡ g x)
    -> f ≡ g
extensionality {A} {B} = ∀-extensionality {A} {λ _ -> B}

-- Function composition
_∘_ : {A B C : Type} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x) 

-- Identity
id : {A : Type} -> A -> A
id x = x

{-
  Exercise 2.3.a
  Definition of the constant map
  Ctx |- A type
  -------------------------------
  Ctx, y : B |- const_y : A -> B
-}
const : {A B : Type} -> A -> B -> A
const x _ = x

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
const-comp-left : {B C : Type}
  -> (A : Type)
  -> (g : B -> C)
  -> (y : B) -> (g ∘ const y) ≡ const (g y)
const-comp-left A g y = ∀-extensionality λ (x : A) -> 
  begin
    (g ∘ const y) x
  ≡⟨⟩
    g (const y x)
  ≡⟨⟩
    g y
  ≡⟨⟩
    const (g y) x
  ∎

{-
  Exercise 2.4.a
  Definition of the swap function
  Ctx |- A type
  Ctx |- B type
  Ctx, x : A, y: B |- (C x y) type
  ---------------------------------------------------------------------------
  Ctx |- swap : ((x : A) -> (y : B) -> C x y) -> ((y : B) -> (x : A) -> C x y)
-}
swap : {A B : Type} {C : A -> B -> Type}
  -> (∀ x -> ∀ y -> C x y)
  -> (∀ y -> ∀ x -> C x y)
swap f y x = f x y

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
      ∀-extensionality λ y -> ?