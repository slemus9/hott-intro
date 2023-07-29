open import Nat.Base
import Nat.Divides as Divides
import Nat.Dist as Dist
open import Function using (id)

module Nat.CongruenceModK where

reflex : ∀ x k -> x ≡ x mod k
reflex x k rewrite Dist.to-itself x = Divides.any-divides-zero k

sym : ∀ x y k -> x ≡ y mod k -> y ≡ x mod k
sym x y k rewrite Dist.commutative x y = id

-- trans : ∀ x y z k
--   -> x ≡ y mod k
--   -> y ≡ z mod k
--   -> x ≡ z mod k
-- trans x y z k = {!   !}
