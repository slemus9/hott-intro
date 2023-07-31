open import Nat.Base
import Nat.Divides as Divides
import Nat.Dist as Dist
open import Function using (id)

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

    dist y z = dist x y + dist x z
    k | dist y z => k | dist x y + dist x z

    k | dist x y and k | dist x y + dist x z => k | dist x z

  3)
    |------|------|    |------|------|
    y      z      x    x      z      y

    dist x y = dist y z + dist x z
    k | dist x y => k | dist y z + dist x z

    k | dist y z and k | dist y z + dist x z => k | dist x z
-}
-- trans : ∀ x y z k
--   -> x ≡ y mod k
--   -> y ≡ z mod k
--   -> x ≡ z mod k
-- trans x y z k = {!   !}
