{-# OPTIONS --rewriting #-}

open import Function using (id; _∘_)

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

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REWRITE _≡_ #-}

  refl-of : {A : Type} -> (x : A) -> x ≡ x
  refl-of x = refl

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

  -- Groupoidal structure of types
  concat : {A : Type} {x y z : A} 
    -> x ≡ y
    -> y ≡ z
    -> x ≡ z
  concat refl refl = refl

  trans = concat

  inv : {A : Type} {x y : A}
    -> x ≡ y -> y ≡ x 
  inv refl = refl

  sym = inv

  module Concat where
    left-unit : {A : Type} {x y : A}
      -> (p : x ≡ y)
      -> concat refl p ≡ p
    left-unit refl = refl

    right-unit : {A : Type} {x y : A}
      -> (p : x ≡ y)
      -> concat p refl ≡ p
    right-unit refl = refl

    assoc : {A : Type} {x y z w : A}
      -> (p : x ≡ y)
      -> (q : y ≡ z)
      -> (r : z ≡ w)
      -> concat (concat p q) r ≡ concat p (concat q r)
    assoc refl q r 
      rewrite left-unit q
      | left-unit (concat q r) = refl

    left-inv : {A : Type} {x y : A}
      -> (p : x ≡ y)
      -> concat (inv p) p ≡ refl
    left-inv refl = refl

    right-inv : {A : Type} {x y : A}
      -> (p : x ≡ y)
      -> concat p (inv p) ≡ refl
    right-inv refl = refl

  {-
    Action on identification of functions
    Every function preserves identification. This is a form of continuity for
    functions in type theory. If there is an identification that identifies two
    points x, y : A, then there is also an identification that identifies the values
    f(x) and f(y) in the codomain of f
  -}
  -- Action on paths
  ap : {A B : Type} {x y : A}
    -> (f : A -> B)
    -> x ≡ y
    -> f x ≡ f y
  ap f refl = refl

  cong = ap

  module Ap where
    ap-id : {A : Type} {x y : A}
      -> (p : x ≡ y)
      -> ap id p ≡ p
    ap-id refl = refl

    ap-comp : {A B C : Type} {x y : A}
      -> (g : B -> C)
      -> (f : A -> B)
      -> (p : x ≡ y)
      -> ap g (ap f p) ≡ ap (g ∘ f) p
    ap-comp g f refl = refl

    ap-refl : {A B : Type}
      -> (f : A -> B)
      -> (x : A)
      -> ap f (refl-of x)  ≡ (refl-of (f x))
    ap-refl f x = refl
    
    ap-inv : {A B : Type} {x y : A}
      -> (f : A -> B)
      -> (p : x ≡ y)
      -> ap f (inv p) ≡ inv (ap f p)
    ap-inv f refl = refl

    ap-concat : {A B : Type} {x y z : A}
      -> (f : A -> B)
      -> (p : x ≡ y)
      -> (q : y ≡ z)
      -> ap f (concat p q) ≡ concat (ap f p) (ap f q)
    ap-concat f refl refl = refl
