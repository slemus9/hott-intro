open import Fin.Base
open import Nat
import Nat.Dist as Dist
import Nat.Less as Less
import Nat.Divides as Divides
import Nat.CongruenceModK as CMK
open CMK.Reasoning
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

incl-first : ∀ k -> incl (first {k}) ≡ zero
incl-first zero = refl
incl-first (suc k) = incl-first k

incl-to-next-fin : ∀ {k}
  -> (x : Fin k)
  -> incl (to-next-fin x) ≡ incl x + 1
incl-to-next-fin base = refl
incl-to-next-fin (i x) = incl-to-next-fin x

incl-next-mod-k : ∀ {k}
  -> (x : Fin k)
  -> incl (next x) ≡ incl x + 1 mod k
incl-next-mod-k {suc k} base rewrite incl-first k = Divides.reflex (suc k)
incl-next-mod-k {suc k} (i x) rewrite incl-to-next-fin x | Dist.to-itself (incl x) = Divides.any-divides-zero (suc k)

{-
  Goal:
      incl [ suc n ] ≡ suc n mod suc k
  ->  incl (next [ n ]) ≡ suc n mod suc k

  IH:
      incl [ n ] ≡ n mod suc k
  ->  suc (incl [ n ]) ≡ suc n mod suc k


  By transitivity of:
    incl (next [ n ]) ≡ suc (incl [ n ]) mod suc k
    suc (incl [ n ]) ≡ suc n mod suc k
  We get:
    incl (next [ n ]) ≡ suc n mod suc k
-}
incl-quotient-map-mod-k+1 : ∀ {k}
  -> (n : Nat)
  -> incl {suc k} [ n ] ≡ n mod (k + 1)
incl-quotient-map-mod-k+1 {k} zero rewrite incl-first k = CMK.reflex zero (k + 1)
incl-quotient-map-mod-k+1 (suc n) =
    incl (next [ n ])
  ≡⟨ incl-next-mod-k [ n ] ⟩
    incl-quotient-map-mod-k+1 n
