import Fin.CyclicInt.Add as Add
import Fin.Incl as Incl
import Fin.NatModK+1 as NatModK+1
import Nat.Add
import Nat.Dist as Dist
import Nat.CongruenceModK as CMK
open CMK.Reasoning
open import DependentPair using (_,_)
open import Fin.Base
open import Fin.CyclicInt.Base
open import Function using (_$_)
open import Identity using (_≡_; refl; sym)
open import Nat hiding (add; zero)

module Fin.CyclicInt.Inv where

{-
    add x (inv x)
  = [ incl x + incl (inv x) ]
  = [ incl x + incl [ dist (incl x) (suc k) ] ]

  zero = [ incl zero ]

  Show that: incl x + incl [ dist (incl x) (suc k) ] ≡ incl zero mod (suc k)
    Since incl [ dist (incl x) (suc k) ] ≡ dist (incl x) (suc k) mod (suc k):
      incl x + incl [ dist (incl x) (suc k) ] ≡ incl x + dist (incl x) (suc k)

  Since incl x < suc k: incl x + dist (incl x) (suc k) = suc k

  Finally: suc k ≡ 0 mod (suc k)
-}
right-inv : ∀ {k} -> (x : ℤ/ (suc k)) -> add x (inv x) ≡ zero
right-inv {k} x rewrite sym $ NatModK+1.split-surjective {k} zero = ans where

  h3 : (incl x + dist (incl x) (suc k)) ≡ 0 mod (suc k)
  h3 rewrite Nat.Add.commutative (incl x) (dist (incl x) (suc k))
    | Dist.commutative (incl x) (suc k)
    | Dist.dist-when-n<m (Incl.bounded x) = 1 , refl

  h2 : (incl x + incl [ dist (incl x) (suc k) ]⟨ k ⟩) ≡ incl x + dist (incl x) (suc k) mod (suc k)
  h2 = CMK.add-preserves-cong-1
    (incl x)
    (incl [ dist (incl x) (suc k) ])
    (incl x)
    (dist (incl x) (suc k))
    (suc k)
    (CMK.reflex (incl x) (suc k))
    (Incl.incl-map-cong $ dist (incl x) (suc k))

  h1 : (incl x + incl [ dist (incl x) (suc k) ]⟨ k ⟩) ≡ incl (zero {k}) mod (suc k)
  h1 rewrite Incl.incl-first (suc k) =
      incl x + incl [ dist (incl x) (suc k) ]
    ≡⟨ h2 ⟩
      incl x + dist (incl x) (suc k)
    ≡⟨ h3 ⟩
      0
    ∎

  ans : [ incl x + incl [ dist (incl x) (suc k) ]⟨ k ⟩ ]⟨ k ⟩  ≡ [ incl (zero {k}) ]
  ans = NatModK+1.effectiveness-bck k (incl x + incl (inv x)) (incl $ zero {k}) h1

left-inv : ∀ {k} -> (x : ℤ/ (suc k)) -> add (inv x) x ≡ zero
left-inv x rewrite Add.commutative (inv x) x = right-inv x
