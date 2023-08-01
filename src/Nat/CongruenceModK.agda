open import Type using (Type)
open import Nat.Base
import Nat.Leq as Leq
import Nat.Divides as Divides
import Nat.Dist as Dist
open import Identity using (_≡_; ap)
open import Function using (id)
open import DependentPair using (_,_)
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
