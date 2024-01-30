import Nat.Add as Add
import Nat.CongruenceModK as CMK
import Nat.Dist as Dist
import Fin.Incl as Incl
import Fin.NatModK+1 as NatModK+1
open CMK.Reasoning
open import DependentPair using (_,_)
open import Fin.Base
open import Function using (_$_)
open import Identity using (_≡_; refl; sym)
open import Int using (Int)
open import Nat hiding (zero; add)
open import Type

module Fin.CyclicGroups where

ℤ/_ : Nat -> Type
ℤ/ 0 = Int
ℤ/ (suc k) = Fin (suc k)

zero : ∀ {k} -> Fin (suc k)
zero = first

add : ∀ {k} -> ℤ/ (suc k) -> ℤ/ (suc k) -> ℤ/ (suc k)
add x y = [ incl x + incl y ]

{-
  Example on Fin 6
  1. inv $ i (i (i (i (i (base {0}))))) = [ 6 ] = i (i (i (i (i (base {0}))))) --> 0 + 6 = 6
  2. inv $ i (i (i (i (base {1})))) = [ 5 ] = base {5} --> 1 + 5 = 6
  3. inv $ i (i (i (base {2}))) = [ 4 ] = i (base {4}) --> 2 + 4 = 6
  4. inv $ i (i (base {3})) = [ 3 ] = i (i (base {3})) --> 3 + 3 = 6
  5. inv $ i (base {4}) = [ 2 ] = i (i (i (base {2}))) --> 4 + 2 = 6
  6. inv $ base {5} = [ 1 ] = i (i (i (i (base {1})))) --> 5 + 1 = 6

  If I add any ℤ/ (suc k) with its inv application, I should always get the first element
-}
inv : ∀ {k} -> ℤ/ (suc k) -> ℤ/ (suc k)
inv {k} x = [ dist (incl x) (suc k) ]

-- Properties
incl-add : ∀ {k} -> (x y : ℤ/ (suc k)) -> incl (add x y) ≡ incl x + incl y mod (suc k)
incl-add x y = Incl.i[x]≡xmodk+1 (incl x + incl y)

-- Z / (k + 1) satisfies the laws of abelian groups
commutative : ∀ {k} -> (x y : ℤ/ (suc k)) -> add x y ≡ add y x
commutative x y rewrite Add.commutative (incl x) (incl y) = refl

assoc : ∀ {k} -> (x y z : ℤ/ (suc k)) -> add (add x y) z ≡ add x (add y z)
assoc {k} x y z = NatModK+1.effectiveness-bck k (incl (add x y) + incl z) (incl x + incl (add y z)) h2 where
  left : (incl (add x y) + incl z) ≡ ((incl x + incl y) + incl z) mod (suc k)
  left = CMK.add-preserves-cong-1
    (incl (add x y))
    (incl z)
    (incl x + incl y)
    (incl z)
    (suc k)
    (incl-add x y)
    (CMK.reflex (incl z) (suc k))

  right : (incl x + incl (add y z)) ≡ incl x + (incl y + incl z) mod (suc k)
  right = CMK.add-preserves-cong-1
    (incl x)
    (incl (add y z))
    (incl x)
    (incl y + incl z)
    (suc k)
    (CMK.reflex (incl x) (suc k))
    (incl-add y z)

  h1 : ((incl x + incl y) + incl z) ≡ incl x + (incl y + incl z) mod (suc k)
  h1 rewrite Add.assoc (incl x) (incl y) (incl z) =
    CMK.reflex (incl x + (incl y + incl z)) (suc k)

  h2 : (incl (add x y) + incl z) ≡ incl x + incl (add y z) mod (suc k)
  h2 =
      incl (add x y) + incl z
    ≡⟨ left ⟩
      (incl x + incl y) + incl z
    ≡⟨ h1 ⟩
      incl x + (incl y + incl z)
    ≡⟨ CMK.sym (incl x + incl (add y z)) (incl x + (incl y + incl z)) (suc k) right ⟩
      incl x + incl (add y z)
    ∎

right-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> add x zero ≡ x
right-unit {k} x rewrite Incl.incl-first k = NatModK+1.split-surjective x

left-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> add zero x ≡ x
left-unit x rewrite commutative zero x = right-unit x

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
  h3 rewrite Add.commutative (incl x) (dist (incl x) (suc k))
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
    (Incl.i[x]≡xmodk+1 $ dist (incl x) (suc k))

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
left-inv x rewrite commutative (inv x) x = right-inv x

{-
  Exercise 7.4
-}
add-one : ∀ {k} -> (x : ℤ/ (suc k)) -> next x ≡ add x one
add-one {Nat.zero} base = refl
add-one {suc k} x
  rewrite Incl.incl-one k
  | Add.right-suc (incl x) 0
  | NatModK+1.split-surjective x = refl
