open import Type using (Type)
open import Nat using (Nat; zero; suc; _+_; _*_)
open import Function using (id)
open import Identity using (_≡_; refl)

module List.Base where

data List (A : Type) : Type where
  nil : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

----------------
-- Operations --
----------------

{-
  Exercise 4.4.a

  Induction Principle:
  Ctx, xs : List A  |- P xs type
  Ctx               |- pNil : P nil
  Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
  -----------------------------------------------------------------
  Ctx, xs : List A  |- ind-list(pNil, pCons, xs) : P xs

  Computation Rules
  Ctx, xs : List A  |- P xs type
  Ctx               |- pNil : P nil
  Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
  -----------------------------------------------------------------
  Ctx               |- ind-list(pNil, pCons, nil) = pNil : P nil

  Ctx, xs : List A  |- P xs type
  Ctx               |- pNil : P nil
  Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
  -----------------------------------------------------------------
  Ctx, x : A, xs : List A |- ind-list(pNil, pCons, x :: xs) = pCons(x, xs, ind-list(pNil, pCons, xs)) : P (x :: xs)
-}
ind-list : {A : Type} {P : List A -> Type}
  -> P nil
  -> (∀ x -> ∀ xs -> P xs -> P (x :: xs))
  -> (xs : List A) -> P xs
ind-list pNil _ nil = pNil
ind-list pNil pCons (x :: xs) = pCons x xs (ind-list pNil pCons xs)

{-
  Exercise 4.4.b
  fold
-}
foldr : {A B : Type}
  -> B
  -> (A -> B -> B)
  -> List A -> B
foldr z op = ind-list z (λ x -> λ _ -> λ next -> op x next)

{-
  Exercise 4.4.c
  map
-}
map : {A B : Type}
  -> (A -> B)
  -> List A -> List B
map f = foldr nil (λ x -> λ next -> f x :: next)

{-
  Exercise 4.4.d
  length
-}
length : {A : Type} -> List A -> Nat
length = foldr zero (λ _ -> λ next -> suc next)

_ : length (4 :: 5 :: 1 :: 2 :: 6 :: 10 :: nil) ≡ 6
_ = refl

{-
  Exercise 4.4.e
  sum and product
-}
sum : List Nat -> Nat
sum = foldr 0 _+_

product : List Nat -> Nat
product = foldr 1 _*_

_ : sum (4 :: 5 :: 1 :: 2 :: 6 :: 10 :: nil) ≡ 28
_ = refl

_ : product (4 :: 5 :: 1 :: 2 :: nil) ≡ 40
_ = refl

{-
  Exercise 4.4.f
  concatenate two lists
-}
_++_ : {A : Type} -> List A -> List A -> List A
xs ++ ys = foldr ys _::_ xs

infixr 5 _++_

_ : (1 :: 10 :: 4 :: 5 :: nil) ++ (3 :: 2 :: 9 :: nil) ≡ (1 :: 10 :: 4 :: 5 :: 3 :: 2 :: 9 :: nil)
_ = refl

{-
  Exercise 4.4.g
  concatenate two lists
-}
flatten : {A : Type} -> List (List A) -> List A
flatten = foldr nil _++_

_ : flatten ((1 :: 2 :: 3 :: nil) :: (4 :: nil) :: (5 :: 6 :: nil) :: nil) ≡ (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil)
_ = refl

{-
  Exercise 4.4.h
  reverse a list
-}
reverse : {A : Type} -> List A -> List A
reverse xs = foldr id (λ x -> λ next -> λ acc -> next (x :: acc)) xs nil

_ : reverse (1 :: 2 :: 3 :: 4 :: 5 :: nil) ≡ (5 :: 4 :: 3 :: 2 :: 1 :: nil)
_ = refl
