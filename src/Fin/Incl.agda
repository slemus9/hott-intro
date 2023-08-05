open import Fin.Base
open import Nat
import Nat.Dist as Dist
import Nat.Less as Less
import Nat.Divides as Divides
import Nat.CongruenceModK as CMK
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

incl-first : ∀ {k} -> incl (first {k}) ≡ zero
incl-first {zero} = refl
incl-first {suc k} = incl-first {k}

incl-to-next-fin : ∀ {k}
  -> (x : Fin k)
  -> incl (to-next-fin x) ≡ incl x + 1
incl-to-next-fin base = refl
incl-to-next-fin (i x) = incl-to-next-fin x

incl-next-mod-k : ∀ {k}
  -> (x : Fin k)
  -> incl (next x) ≡ incl x + 1 mod k
incl-next-mod-k {suc k} base rewrite incl-first {k} = Divides.reflex (suc k)
incl-next-mod-k {suc k} (i x) rewrite incl-to-next-fin x | Dist.to-itself (incl x) = Divides.any-divides-zero (suc k)
