open import Fin.Base
open import Fin.Incl
open import Nat
import Nat.CongruenceModK as CMK
open CMK.Reasoning
open import Identity using (_≡_; refl)

module Fin.NatModK+1 where

effectiveness-fwd : ∀ k x y
  -> [ x ]⟨ k ⟩ ≡ [ y ]⟨ k ⟩
  -> x ≡ y mod (suc k)
effectiveness-fwd k x y [x]≡[y] =
    x
  ≡⟨ lemma1 ⟩
    incl [ x ]⟨ k ⟩
  ≡⟨ lemma2 ⟩
    incl [ y ]⟨ k ⟩
  ≡⟨ incl-quotient-map-mod-k+1 y ⟩
    y
  ∎
  where
    lemma1 : x ≡ incl [ x ]⟨ k ⟩ mod (suc k)
    lemma1 = CMK.sym (incl [ x ]⟨ k ⟩) x (suc k) (incl-quotient-map-mod-k+1 x)

    lemma2 : incl [ x ]⟨ k ⟩  ≡ incl [ y ]⟨ k ⟩ mod (suc k)
    lemma2 rewrite [x]≡[y] = CMK.reflex (incl [ y ]) (suc k)


effectiveness-bck : ∀ k x y
  -> x ≡ y mod k
  -> [ x ]⟨ suc k ⟩ ≡ [ y ]⟨ suc k ⟩
effectiveness-bck = {!   !}
