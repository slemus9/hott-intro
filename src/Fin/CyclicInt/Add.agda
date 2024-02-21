import Nat.CongruenceModK as CMK
import Fin.Incl as Incl
import Fin.NatModK+1 as NatModK+1
import Nat.Add as Add
open CMK.Reasoning
open import Fin.Base
open import Fin.CyclicInt.Base
open import Function using (_$_)
open import Identity using (_≡_; ap; refl; sym)
open import Nat hiding (add; zero)

module Fin.CyclicInt.Add where

incl-add-cong : ∀ {k} -> (x y : ℤ/ (suc k)) -> incl (add x y) ≡ incl x + incl y mod (suc k)
incl-add-cong x y = Incl.incl-map-cong (incl x + incl y)

-- Addition on Z / (k + 1) satisfies the laws of abelian groups
commutative : ∀ {k} -> (x y : ℤ/ (suc k)) -> add x y ≡ add y x
commutative x y = ap [_] (Add.commutative (incl x) (incl y))

associative : ∀ {k} -> (x y z : ℤ/ (suc k)) -> add (add x y) z ≡ add x (add y z)
associative {k} x y z = NatModK+1.effectiveness-bck k (incl (add x y) + incl z) (incl x + incl (add y z)) res where
  left : (incl (add x y) + incl z) ≡ ((incl x + incl y) + incl z) mod (suc k)
  left = CMK.add-preserves-cong-1
    (incl (add x y))
    (incl z)
    (incl x + incl y)
    (incl z)
    (suc k)
    (incl-add-cong x y)
    (CMK.reflex (incl z) (suc k))

  right : (incl x + incl (add y z)) ≡ incl x + (incl y + incl z) mod (suc k)
  right = CMK.add-preserves-cong-1
    (incl x)
    (incl (add y z))
    (incl x)
    (incl y + incl z)
    (suc k)
    (CMK.reflex (incl x) (suc k))
    (incl-add-cong y z)

  res : (incl (add x y) + incl z) ≡ incl x + incl (add y z) mod (suc k)
  res =
      incl (add x y) + incl z
    ≡⟨ left ⟩
      (incl x + incl y) + incl z
    ≡⟨ CMK.when-eq (suc k) $ Add.associative (incl x) (incl y) (incl z) ⟩
      incl x + (incl y + incl z)
    ≡⟨ CMK.sym (incl x + incl (add y z)) (incl x + (incl y + incl z)) (suc k) right ⟩
      incl x + incl (add y z)
    ∎

right-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> add x zero ≡ x
right-unit {k} x rewrite Incl.incl-first k = NatModK+1.split-surjective x

left-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> add zero x ≡ x
left-unit x rewrite commutative zero x = right-unit x

{-
  Exercise 7.4
-}
add-one : ∀ {k} -> (x : ℤ/ (suc k)) -> next x ≡ add x one
add-one {Nat.zero} base = refl
add-one {suc k} x
  rewrite Incl.incl-one k
  | Add.right-suc (incl x) 0
  | NatModK+1.split-surjective x = refl
