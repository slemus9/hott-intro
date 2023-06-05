open import Type using (Type)

module Function where

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

_$_ : {A : Type} {B : A -> Type} 
  -> (∀ x -> B x) 
  -> ∀ x -> B x
f $ x = f x
