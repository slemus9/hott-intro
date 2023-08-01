open import Fin.Base
open import Nat
import Nat.Less as Less
open import Function using (_∘_; _$_)
open import Identity using (_≡_; refl; ap; sym)
open import Empty using (ex-falso)

module Fin.Incl where

bounded : ∀ k -> (x : Fin k) -> incl k x < k
bounded (suc k) base = Less.n<s
bounded (suc k) (i x) = Less.right-suc (bounded k x)

injective : ∀ k -> (x y : Fin k) -> incl k x ≡ incl k y -> x ≡ y
injective (suc k) base base _ = refl
injective (suc k) base (i y) eq = ex-falso $ Less.when-equal (sym eq) (bounded k y)
injective (suc k) (i x) base eq = ex-falso $ Less.when-equal eq (bounded k x)
injective (suc k) (i x) (i y) = ap i ∘ injective k x y
