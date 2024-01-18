open import Type using (Type)
open import Nat.Base
import Nat.Add as Add
import Nat.Leq as Leq
import Nat.Divides as Divides
import Nat.Dist as Dist
open import Identity using (_≡_; ap)
open import Function using (id; _$_)
open import DependentPair using (_,_; _<-->_; fst; snd)
open import Coproduct using (_⨄_; inl; inr)

module Nat.CongruenceModK where

reflex : ∀ x k -> x ≡ x mod k
reflex x k rewrite Dist.to-itself x = Divides.any-divides-zero k

sym : ∀ x y k -> x ≡ y mod k -> y ≡ x mod k
sym x y k rewrite Dist.commutative x y = id

{-
  k | dist x y = (k1, k * k1 = dist x y)
  k | dist y z = (k2, k * k2 = dist y z)

  Cases:

  1)
    |------|------|    |------|------|
    x      y      z    z      y      x

    dist x z = dist x y + dist y z
    k | dist x y and k | dist y z
      => k | dist x y + dist y z
      => k | dist x z

  2)
    |------|------|    |------|------|
    y      x      z    z      x      y

    dist y z = dist y x + dist x z
    k | dist y z => k | dist y x + dist x z

    k | dist y x and k | dist y x + dist x z => k | dist x z

  3)
    |------|------|    |------|------|
    y      z      x    x      z      y

    dist y x = dist y z + dist z x
    k | dist y x => k | dist y z + dist z x

    k | dist y z and k | dist y z + dist z x => k | dist z x
-}
trans : ∀ x y z k
  -> x ≡ y mod k
  -> y ≡ z mod k
  -> x ≡ z mod k
trans x y z k c1 c2 = cases (Leq.total x y) (Leq.total y z) (Leq.total x z) where
  Total : Nat -> Nat -> Type
  Total x y = (x ≤ y) ⨄ (y ≤ x)

  case1 : dist x z ≡ dist x y + dist y z -> x ≡ z mod k
  case1 eq rewrite eq = Divides.divides-x-y-then-x+y k (dist x y) (dist y z) c1 c2

  case2 : dist y z ≡ dist y x + dist x z -> y ≡ z mod k -> x ≡ z mod k
  case2 eq rewrite eq = Divides.divides-x-x+y-then-y k (dist y x) (dist x z) (sym x y k c1)

  case3 : dist y x ≡ dist y z + dist z x -> x ≡ y mod k -> x ≡ z mod k
  case3 eq rewrite Dist.commutative y x | Dist.commutative z x | eq =
    Divides.divides-x-x+y-then-y k (dist y z) (dist x z) c2

  cases : Total x y -> Total y z -> Total x z -> x ≡ z mod k
  cases (inl x≤y) (inl y≤z) (inl x≤z) = case1 (Dist.dist-through-fwd x≤y y≤z)
  cases (inl x≤y) (inl y≤z) (inr z≤x) = case1 (Dist.dist-through-fwd x≤y y≤z)
  cases (inl x≤y) (inr z≤y) (inl x≤z) = case3 (Dist.dist-through-bck x≤z z≤y) c1
  cases (inl x≤y) (inr z≤y) (inr z≤x) = case2 (Dist.dist-through-bck z≤x x≤y) c2
  cases (inr y≤x) (inl y≤z) (inl x≤z) = case2 (Dist.dist-through-fwd y≤x x≤z) c2
  cases (inr y≤x) (inl y≤z) (inr z≤x) = case3 (Dist.dist-through-fwd y≤z z≤x) c1
  cases (inr y≤x) (inr z≤y) (inl x≤z) = case2 (Dist.dist-through-fwd y≤x x≤z) c2
  cases (inr y≤x) (inr z≤y) (inr z≤x) = case1 (Dist.dist-through-bck z≤y y≤x)

module Reasoning where
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  _≡⟨⟩_ : ∀ x {y k}
    -> x ≡ y mod k
    -> x ≡ y mod k
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ x {y z k}
    -> x ≡ y mod k
    -> y ≡ z mod k
    -> x ≡ z mod k
  _≡⟨_⟩_ x {y} {z} {k} x≡y y≡z = trans x y z k x≡y y≡z

  _∎ : ∀ x {k}
    -> x ≡ x mod k
  _∎ x {k} = reflex x k

open Reasoning

add1 : ∀ {x y k} -> x ≡ y mod k -> suc x ≡ suc y mod k
add1 = id

add-left : ∀ a b c k
  -> (a ≡ b mod k) <--> ((c + a) ≡ c + b mod k)
add-left a b c k rewrite Dist.invariant c a b = id , id

add-left-fwd : ∀ a b c k
  -> a ≡ b mod k
  -> (c + a) ≡ c + b mod k
add-left-fwd a b c k = fst (add-left a b c k)

add-left-bck : ∀ a b c k
  -> (c + a) ≡ c + b mod k
  -> a ≡ b mod k
add-left-bck a b c k = snd (add-left a b c k)

add-right : ∀ a b c k
  -> (a ≡ b mod k) <--> ((a + c) ≡ b + c mod k)
add-right a b c k rewrite Add.commutative a c | Add.commutative b c = add-left a b c k

add-right-fwd : ∀ a b c k
  -> a ≡ b mod k
  -> (a + c) ≡ b + c mod k
add-right-fwd a b c k = fst (add-right a b c k)

add-right-bck : ∀ a b c k
  -> (a + c) ≡ b + c mod k
  -> a ≡ b mod k
add-right-bck a b c k = snd (add-right a b c k)

{-
  x ≡ x' mod k -> x + y ≡ x' + y mod k
  y ≡ y' mod k -> x' + y ≡ x' + y' mod k
-}
add-preserves-cong-1 : ∀ x y x' y' k
  -> x ≡ x' mod k
  -> y ≡ y' mod k
  -> (x + y) ≡ x' + y' mod k
add-preserves-cong-1 x y x' y' k x≡x' y≡y' =
    x + y
  ≡⟨ add-right-fwd x x' y k x≡x' ⟩
    x' + y
  ≡⟨ add-left-fwd y y' x' k y≡y' ⟩
    x' + y'
  ∎

{-
  x ≡ x' mod k -> x + y' ≡ x' + y' mod k

     x + y ≡ x' + y' mod k
  && x + y' ≡ x' + y' mod k
  -> x + y ≡ x + y' mod k
  -> y ≡ y' mod k
-}
add-preserves-cong-2 : ∀ x y x' y' k
  -> x ≡ x' mod k
  -> (x + y) ≡ x' + y' mod k
  -> y ≡ y' mod k
add-preserves-cong-2 x y x' y' k x≡x' x+y≡x'+y' = add-left-bck y y' x k x+y≡x+y' where
  x+y≡x+y' : (x + y) ≡ x + y' mod k
  x+y≡x+y' =
      x + y
    ≡⟨ x+y≡x'+y' ⟩
      x' + y'
    ≡⟨ sym (x + y') (x' + y') k $ add-right-fwd x x' y' k x≡x' ⟩
      x + y'
    ∎

add-preserves-cong-3 : ∀ x y x' y' k
  -> y ≡ y' mod k
  -> (x + y) ≡ x' + y' mod k
  -> x ≡ x' mod k
add-preserves-cong-3 x y x' y' k
  rewrite Add.commutative x y | Add.commutative x' y'  = add-preserves-cong-2 y x y' x' k
