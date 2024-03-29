open import Fin.Base
open import Nat.Base
import Nat.Dist as Dist
import Nat.Leq as Leq
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

injective : ∀ {k} -> {x y : Fin k} -> incl x ≡ incl y -> x ≡ y
injective {_} {base} {base} _ = refl
injective {_} {base} {i y} eq = ex-falso $ Less.when-equal (sym eq) (bounded y)
injective {_} {i x} {base} eq = ex-falso $ Less.when-equal eq (bounded x)
injective {_} {i x} {i y} = ap i ∘ injective

incl-first : ∀ k -> incl (first {k}) ≡ zero
incl-first zero = refl
incl-first (suc k) = incl-first k

incl-to-next-fin : ∀ {k}
  -> (x : Fin k)
  -> incl (to-next-fin x) ≡ incl x + 1
incl-to-next-fin base = refl
incl-to-next-fin (i x) = incl-to-next-fin x

incl-one : ∀ k -> incl (one {suc k}) ≡ 1
incl-one zero = refl
incl-one (suc k)
  rewrite incl-to-next-fin (first {k + 2}) | incl-first (k + 2) = refl

incl-next-cong : ∀ {k}
  -> (x : Fin k)
  -> incl (next x) ≡ incl x + 1 mod k
incl-next-cong {suc k} base rewrite incl-first k = Divides.reflex (suc k)
incl-next-cong {suc k} (i x) rewrite incl-to-next-fin x | Dist.to-itself (incl x) = Divides.any-divides-zero (suc k)

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
incl-quot-map-cong : ∀ {k}
  -> (n : Nat)
  -> incl [ n ]⟨ k ⟩ ≡ n mod (k + 1)
incl-quot-map-cong {k} zero rewrite incl-first k = CMK.reflex zero (k + 1)
incl-quot-map-cong (suc n) =
    incl (next [ n ])
  ≡⟨ incl-next-cong [ n ] ⟩
    incl-quot-map-cong n

incl-next-leq : ∀ {k}
  -> (x : Fin k)
  -> incl (next x) ≤ suc (incl x)
incl-next-leq {k} base rewrite incl-first k = 0≤n
incl-next-leq (i x) rewrite incl-to-next-fin x = s≤s (Leq.when-eq refl)

incl-quot-map-leq : ∀ {k}
  -> (n : Nat)
  -> incl [ n ]⟨ k ⟩ ≤ n
incl-quot-map-leq {k} zero rewrite incl-first k = 0≤n
incl-quot-map-leq (suc n) = Leq.trans (incl-next-leq [ n ]) (s≤s (incl-quot-map-leq n))
