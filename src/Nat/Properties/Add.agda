open import Type using (Type)
open import Nat using (Nat; zero; suc; ind-nat; _+_)
open import Identity using (_≡_; refl; ap)

module Nat.Properties.Add where

right-unit : (n : Nat) -> n + 0 ≡ n
right-unit _ = refl

left-unit : (n : Nat) -> 0 + n ≡ n
left-unit = ind-nat refl λ _ p -> ap suc p

-- m + suc n = suc (m + n)
right-suc : (m n : Nat) -> m + suc n ≡ suc (m + n)
right-suc m n = refl

-- suc m + suc n = suc (suc m + n)
-- suc (m + suc n) = suc (suc (m + n))
left-suc : (m n : Nat) -> suc m + n ≡ suc (m + n)
left-suc m = ind-nat p0 pSuc
  where
    p0 : suc m + 0 ≡ suc (m + 0)
    p0 = refl

    pSuc : (n : Nat) -> suc m + n ≡ suc (m + n) -> suc m + suc n ≡ suc (m + suc n)
    pSuc n p = ap suc p

{-
  (m + n) + suc k = suc ((m + n) + k)
  m + (n + suc k) = m + suc (n + k) = suc (m + (n + k))
-}
assoc : (m n k : Nat) -> (m + n) + k ≡ m + (n + k)
assoc m n = ind-nat p0 pSuc
  where
    P : Nat -> Type
    P k = (m + n) + k ≡ m + (n + k)

    p0 : P 0
    p0 = refl

    pSuc : (k : Nat) -> P k -> P (suc k)
    pSuc k p = ap suc p

{-
  m + suc n = suc (m + n)
  suc n + m = suc (m + n)
-}
commutative : (m n : Nat) -> m + n ≡ n + m
commutative m zero 
  rewrite left-unit m = refl
commutative m (suc n)
  rewrite left-suc n m = ap suc (commutative m n)
