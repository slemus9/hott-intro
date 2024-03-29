open import Type using (Type)
open import Function.Base using (id)
open import DependentPair using (Σ; _,_)
open import Empty.Negation.Base using (¬_)

module Identity.Base where

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

refl-of : {A : Type} -> (x : A) -> x ≡ x
refl-of x = refl

----------------
-- Operations --
----------------

{-
  Induction principle. Also called identification elimination or path induction
  An element of type a ≡ x is also called identification or path.

  Ctx |- a : A
  Ctx, x : A, p : a ≡ x |- P x p type
  -----------------------------------------------------------------
  Ctx |- ind-eq a : P a refl -> (x : A) -> (p : a ≡ x) -> P x p

  Computation rule:
  Ctx |- a : A
  Ctx, x : A, p : a ≡ x |- P x p type
  -----------------------------------------------------------------
  Ctx, u : P a refl |- ind-eq u a refl = u : P a refl
-}
ind-eq : {A : Type} {a : A} {P : (x : A) -> a ≡ x -> Type}
  -> P a refl
  -> ∀ x -> (p : a ≡ x) -> P x p
ind-eq u a refl = u

-- Groupoidal structure of types
concat : {A : Type} {x y z : A}
  -> x ≡ y
  -> y ≡ z
  -> x ≡ z
concat refl = id

trans = concat

inv : {A : Type} {x y : A}
  -> x ≡ y -> y ≡ x
inv refl = refl

sym = inv

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

{-
  Transport.
  We can trasport any element b : B x to the fiber B y
-}
tr : {A : Type} {B : A -> Type} {x y : A}
  -> x ≡ y
  -> B x -> B y
tr refl = id

-- Dependent action on paths
adp : {A : Type} {B : A -> Type} {x y : A}
  -> (f : ∀ a -> B a)
  -> (p : x ≡ y)
  -> tr p (f x) ≡ f y
adp f refl = refl

{-
  We cannot show that p ≡ refl-of a for any p : a ≡ a using the
  induction principle of identity types, but we can show that the pair (a, relf-of a) is unique;
  that is, there is (up to identification) only one element in
  Σ-type of the identity type. These types are called contractible
-}
uniq-Σ-identification : {A : Type}
  -> (a : A)
  -> (y : Σ A (a ≡_))
  -> (a , refl) ≡ y
uniq-Σ-identification a (.a , refl) = refl

{-
  Exercise 5.3
  Analogous to the path lifting property for fibrations in
  homotopy theory
-}
lift : {A : Type} {B : A -> Type} {a x : A}
  -> (p : a ≡ x)
  -> (b : B a)
  -> Σ A B
lift {_} {_} {_} {x} p b = x , tr p b

_≢_ : {A : Type} -> A -> A -> Type
x ≢ y = ¬ (x ≡ y)

infix 4 _≢_
