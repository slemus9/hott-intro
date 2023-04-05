module Identity where

  Type = Set

  {-
    The identity type:
    - An inductive type with a reflexivity identification
    - The identity type is an inductive family of types

    Type formation rule:
    Ctx |- a : A
    ------------------------
    Ctx, x : A |- a ≡ x type

    Introduction rule:
    Ctx |- a : A
    ------------------------
    Ctx |- refl a : a ≡ a
  -}
  data _≡_ {A : Type} (x : A) : A -> Type where
    refl : x ≡ x

  infix 4 _≡_

  {-  
    Induction principle. Also called identification elimination or path induction
    An element of type a ≡ x is also called identification or path.

    Ctx |- a : A
    Ctx, a : A, x : A, p : a ≡ x |- P a x p type
    -----------------------------------------------------------------
    Ctx |- ind-eq a : P a a refl -> (x : A) -> (p : a ≡ x) -> P a x p 

    Computation rule:
    Ctx |- a : A
    Ctx, a : A, x : A, p : a ≡ x |- P a x p type
    -----------------------------------------------------------------
    Ctx, u : P a a refl |- ind-eq a u a refl : P a a refl
  -}
  ind-eq : {A : Type} {P : (a x : A) -> a ≡ x -> Type}
    -> ∀ a
    -> P a a refl
    -> ∀ x -> (p : a ≡ x) -> P a x p
  ind-eq a u .a refl = u
