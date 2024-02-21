import Nat.CongruenceModK as CMK
import Fin.Incl as Incl
import Nat.Mul as Mul
import Fin.NatModK+1 as NatModK+1
open CMK.Reasoning
open import Fin.Base
open import Fin.CyclicInt.Base
open import Function using (_$_)
open import Nat hiding (add; mul; zero)
open import Identity using (_≡_; ap; refl)

module Fin.CyclicInt.Mul where

{-
  Exercise 7.8.a
-}
incl-mul-cong : ∀ {k}
  -> (x y : ℤ/ (suc k))
  -> incl (mul x y) ≡ incl x * incl y mod (suc k)
incl-mul-cong x y = Incl.incl-map-cong (incl x * incl y)

{-
  Exercise 7.8.c

  Multiplication on Z / (k + 1) satisfies the laws of a commutative ring
-}
commutative : ∀ {k}
  -> (x y : ℤ/ (suc k))
  ->  mul x y ≡ mul y x
commutative x y = ap [_] (Mul.commutative (incl x) (incl y))

associative : ∀ {k}
  -> (x y z : ℤ/ (suc k))
  -> mul (mul x y) z ≡ mul x (mul y z)
associative {k} x y z =
  NatModK+1.effectiveness-bck
    k
    (incl (mul x y) * incl z)
    (incl x * incl (mul y z))
    res
  where
    left-cong : (incl (mul x y) * incl z) ≡ (incl x * incl y) * incl z mod (suc k)
    left-cong = CMK.mul-preserves-cong
      (incl (mul x y))
      (incl z)
      (incl x * incl y)
      (incl z)
      (suc k)
      (Incl.incl-map-cong $ incl x * incl y)
      (CMK.reflex (incl z) (suc k))

    right-cong : (incl x * incl (mul y z)) ≡ incl x * (incl y * incl z) mod (suc k)
    right-cong = CMK.mul-preserves-cong
      (incl x)
      (incl $ mul y z)
      (incl x)
      (incl y * incl z)
      (suc k)
      (CMK.reflex (incl x) (suc k))
      (Incl.incl-map-cong $ incl y * incl z)

    res : (incl (mul x y) * incl z) ≡ (incl x * incl (mul y z)) mod (suc k)
    res =
        incl (mul x y) * incl z
      ≡⟨ left-cong ⟩
        (incl x * incl y) * incl z
      ≡⟨ CMK.when-eq (suc k) $ Mul.associative (incl x) (incl y) (incl z) ⟩
        incl x * (incl y * incl z)
      ≡⟨ CMK.sym (incl x * incl (mul y z)) (incl x * (incl y * incl z)) (suc k) right-cong ⟩
        incl x * incl (mul y z)
      ∎

right-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> mul x one ≡ x
right-unit {Nat.zero} base rewrite Incl.incl-first 0 = refl
right-unit {suc k} x
  rewrite Incl.incl-one k
  | Mul.right-unit (incl x) = NatModK+1.split-surjective x

left-unit : ∀ {k} -> (x : ℤ/ (suc k)) -> mul one x ≡ x
left-unit x rewrite commutative one x = right-unit x
