import Fin.Incl as Incl
import Nat.Add as Add
import Nat.Dist as Dist
import Nat.Mul as Mul
open import DependentPair using (_,_)
open import Empty using (ex-falso)
open import Fin.Base
open import Function using (_$_)
open import Nat.Base
open import Identity using (_≡_; refl; sym)

module Nat.Division where

{-
  Exercise 7.9.a
-}
euclidean-div : ∀ a b -> Division a b
euclidean-div a zero = record
  { quotient = 0
  ; remainder = a
  ; when-divisor-positive = λ b≢0 -> ex-falso (b≢0 refl)
  ; division = sym (Add.left-unit a)
  }
euclidean-div a (suc b) with Incl.incl-quot-map-cong {b} a
... | k , sb*k≡a-r = record
  { quotient = k
  ; remainder = incl [ a ]⟨ b ⟩
  ; when-divisor-positive = λ _ -> Incl.bounded [ a ]
  ; division = division
  } where
    division : a ≡ k * (suc b) + incl [ a ]⟨ b ⟩
    division rewrite Mul.commutative k (suc b)
      | sb*k≡a-r
      | Dist.commutative (incl [ a ]⟨ b ⟩) a = sym $ Dist.dist-when-n≤m (Incl.incl-quot-map-leq a)
