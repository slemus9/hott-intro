module DependentPair where

  Type = Set

  data Σ (A : Type) (B : A -> Type) : Type where
    pair : (x : A) -> (y : B x) -> Σ A B

  -- Induction principle
  -- This is also the uncurrying function
  ind-Σ : {A : Type} {B : A -> Type} {P : Σ A B -> Type}
    -> (∀ x -> ∀ y -> P (pair x y))
    -> (z : Σ A B) -> P z
  ind-Σ f (pair x y) = f x y

  -- First projection map
  pr1 : {A : Type} {B : A -> Type}
    -> Σ A B -> A
  pr1 (pair x y) = x

  -- Second projection map
  pr2 : {A : Type} {B : A -> Type}
    -> (z : Σ A B) -> B (pr1 z)
  pr2 (pair x y) = y

  curry : {A : Type} {B : A -> Type} {P : Σ A B -> Type}
    -> (∀ z -> P z)
    -> ∀ x -> ∀ y -> P (pair x y)
  curry f x y = f (pair x y)

  -- The product is a special case of Σ
  _×_ : Type -> Type -> Type
  A × B = Σ A (λ _ -> B)
