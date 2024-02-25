import Fin.Incl as Incl
import Nat.Add as Add
import Nat.Dist as Dist
import Nat.Less as Less
import Nat.Mul as Mul
open import DependentPair using (Σ; _×_; _,_)
open import Empty using (ex-falso)
open import Fin.Base
open import Function using (_$_)
open import Nat.Base
open import Identity using (_≢_; _≡_; refl; sym)

module Nat.Division where

{-
  Alternative definition for Euclidean Division:
  TODO: How to prove that incl [ a ]⟨ k ⟩ ≤ a ?
-}
-- euclidean-div a zero = record
--   { quotient = 0
--   ; remainder = a
--   ; when-divisor-positive = λ b≢0 -> ex-falso (b≢0 refl)
--   ; division = sym (Add.left-unit a)
--   }
-- euclidean-div a (suc b) with Incl.incl-map-cong {b} a
-- ... | k , sb*k≡a-r = record
--   { quotient = k
--   ; remainder = incl [ a ]⟨ b ⟩
--   ; when-divisor-positive = λ _ -> Incl.bounded [ a ]
--   ; division = division
--   }
--   where
--     division : a ≡ k * (suc b) + incl [ a ]⟨ b ⟩
--     division
--       rewrite Mul.commutative k (suc b)
--       | sb*k≡a-r
--       | Dist.commutative (incl [ a ]⟨ b ⟩) a = sym (Dist.dist-when-n≤m {!   !})

{-
  Exercise 7.9.a
-}
euclidean-div : ∀ a b -> Division a b
euclidean-div-low : ∀ {a b} -> a < b -> Division a b
euclidean-div-middle : ∀ {a b} -> a ≡ b -> Division a b
euclidean-div-high : ∀ {a b} -> b < a -> Division a b

euclidean-div a b with Less.connected a b
... | Less.Connected.low a<b = euclidean-div-low a<b
... | Less.Connected.middle a≡b = euclidean-div-middle a≡b
... | Less.Connected.high b<a = euclidean-div-high b<a

euclidean-div-low {a} {b} a<b = record
  { quotient = 0
  ; remainder = a
  ; when-divisor-positive = λ _ -> a<b
  ; division = division
  }
  where
    division : a ≡ 0 * b + a
    division rewrite Mul.left-zero b = sym (Add.left-unit a)

euclidean-div-middle {a} {_} refl = record
  { quotient = 1
  ; remainder = 0
  ; when-divisor-positive = Less.when-not-zero
  ; division = sym (Mul.left-unit a)
  }

euclidean-div-high {suc a} {zero} 0<s = record
  { quotient = 0
  ; remainder = suc a
  ; when-divisor-positive = λ b≢0 -> ex-falso (b≢0 refl)
  ; division = sym $ Add.left-unit (suc a)
  }
euclidean-div-high {suc a} {suc b} (s<s b<a) with Incl.incl-map-cong {b} (suc a)
... | k , sb*k≡sa-r = record
    { quotient = k
    ; remainder = incl [ suc a ]⟨ b ⟩
    ; when-divisor-positive = λ _ -> Incl.bounded [ suc a ]
    ; division = division
    }
  where
    h : incl [ suc a ]⟨ b ⟩ < suc a
    h = Less.trans (Incl.bounded [ suc a ]⟨ b ⟩) (s<s b<a)

    division : suc a ≡ k * (suc b) + incl [ suc a ]⟨ b ⟩
    division
      rewrite Mul.commutative k (suc b)
      | sb*k≡sa-r
      | Dist.commutative (incl [ suc a ]⟨ b ⟩) (suc a) = sym (Dist.dist-when-n<m h)
