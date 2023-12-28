open import Fin.Base
open import Fin.Incl as Incl
open import Nat
open import Nat.Divides as Divides
open import Nat.Dist as Dist
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
  ≡⟨ Incl.i[x]≡xmodk+1 y ⟩
    y
  ∎
  where
    lemma1 : x ≡ incl [ x ]⟨ k ⟩ mod (suc k)
    lemma1 = CMK.sym (incl [ x ]⟨ k ⟩) x (suc k) (Incl.i[x]≡xmodk+1 x)

    lemma2 : incl [ x ]⟨ k ⟩  ≡ incl [ y ]⟨ k ⟩ mod (suc k)
    lemma2 rewrite [x]≡[y] = CMK.reflex (incl [ y ]) (suc k)

{-
  suc k * j1 ≡ dist x y

     x ≡ incl [ x ] mod (suc k)
  && y ≡ incl [ y ] mod (suc k)
  => incl [ x ] ≡ incl [ y ] mod (suc k)
  => suc k * j2 ≡ dist (incl [ x ]) (incl [ y ])

      incl [ x ] < suc k
      incl [ y ] < suc k
  =>  dist (incl [ x ]) (incl [ y ]) < suc k

     dist (incl [ x ]) (incl [ y ]) < suc k
  && (suc k) divides (dist (incl [ x ]) (incl [ y ]))
  => dist (incl [ x ]) (incl [ y ]) ≡ 0
  => incl [ x ] ≡ incl [ y ]
  => [ x ] ≡ [ y ]
-}
effectiveness-bck : ∀ k x y
  -> x ≡ y mod (suc k)
  -> [ x ]⟨ k ⟩ ≡ [ y ]⟨ k ⟩
effectiveness-bck k x y x≡ymodk+1 = Incl.injective [ x ]⟨ k ⟩ [ y ]⟨ k ⟩ i[x]≡i[y] where
  i[x]≡i[y]modk+1 : incl [ x ]⟨ k ⟩ ≡ incl [ y ]⟨ k ⟩ mod (suc k)
  i[x]≡i[y]modk+1 =
      incl [ x ]⟨ k ⟩
    ≡⟨ Incl.i[x]≡xmodk+1 x ⟩
      x
    ≡⟨ x≡ymodk+1 ⟩
      y
    ≡⟨ CMK.sym (incl [ y ]⟨ k ⟩) y (suc k) (Incl.i[x]≡xmodk+1 y) ⟩
      incl [ y ]⟨ k ⟩
    ∎

  i[x]-i[y]<k+1 : dist (incl [ x ]⟨ k ⟩) (incl [ y ]⟨ k ⟩) < suc k
  i[x]-i[y]<k+1 = Dist.both-less-than-k (Incl.bounded [ x ]⟨ k ⟩) (Incl.bounded [ y ]⟨ k ⟩)

  i[x]-i[y]≡0 : dist (incl [ x ]⟨ k ⟩) (incl [ y ]⟨ k ⟩) ≡ 0
  i[x]-i[y]≡0 = Divides.divisor-less-than-dividend-fwd
    (suc k)
    (dist (incl [ x ]⟨ k ⟩) (incl [ y ]⟨ k ⟩))
    i[x]-i[y]<k+1
    i[x]≡i[y]modk+1

  i[x]≡i[y] : incl [ x ]⟨ k ⟩ ≡ incl [ y ]⟨ k ⟩
  i[x]≡i[y] = Dist.itself-bck (incl [ x ]⟨ k ⟩) (incl [ y ]⟨ k ⟩) i[x]-i[y]≡0
