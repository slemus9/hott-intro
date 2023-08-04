open import Fin.Base
open import Nat
import Nat.Less as Less
open import Function using (_∘_; _$_)
open import Identity using (_≡_; refl; ap; sym)
open import Empty using (ex-falso)

module Fin.Incl where

bounded : ∀ {k} -> (x : Fin k) -> incl x < k
bounded base = Less.n<s
bounded (i x) = Less.right-suc (bounded x)

injective : ∀ {k} -> (x y : Fin k) -> incl x ≡ incl y -> x ≡ y
injective base base _ = refl
injective base (i y) eq = ex-falso $ Less.when-equal (sym eq) (bounded y)
injective (i x) base eq = ex-falso $ Less.when-equal eq (bounded x)
injective (i x) (i y) = ap i ∘ injective x y
