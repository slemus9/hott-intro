open import Nat.Def using (Nat; zero; suc; _+_; _*_)
import Nat.Properties.Add as Add 
open import Identity.Def using (_≡_; refl; ap; inv)

{-
  Exercise 5.5
-}
module Nat.Properties.Mul where

right-zero : (n : Nat) -> n * 0 ≡ 0
right-zero n = refl

left-zero : (n : Nat) -> 0 * n ≡ 0
left-zero zero = refl
left-zero (suc n) 
  rewrite Add.left-unit (0 * n) = left-zero n

-- suc n * (suc 0) = (suc n) + (n * 0)
right-unit : (n : Nat) -> n * 1 ≡ n
right-unit zero = left-zero 1
right-unit (suc n) = refl

{-
    (suc 0) * (suc n) 
  = (suc 0) + ((suc 0) * n)
  = suc (0 + ((suc 0) * n))
-}
left-unit : (n : Nat) -> 1 * n ≡ n
left-unit zero = refl
left-unit (suc n)
  rewrite Add.left-suc 0 ((suc 0) * n)
  | Add.left-unit (1 * n) = ap suc (left-unit n)

right-suc : (m n : Nat) -> m * (suc n) ≡ m + (m * n)
right-suc _ _ = refl

{-
    (suc m) * (suc n)
  = (suc m) + ((suc m) * n)
  = suc (m + (suc m) * n)
  = suc (m + ((m * n) + n))

    (m * suc n) + suc n
  = suc (m * (suc n) + n) 
  = suc ((m + m * n) + n)
-}
left-suc : (m n : Nat) -> (suc m) * n ≡ (m * n) + n
left-suc m zero
  rewrite right-zero (suc m) = refl
left-suc m (suc n)
  rewrite Add.left-suc m (suc m * n)
  | left-suc m n
  | inv (Add.assoc m (m * n) n)  = refl

{-
    m * (suc n)
  = m + m * n
  = m + n * m

  (suc n) * m
  = (n * m) + m
-}
commutative : (m n : Nat) -> m * n ≡ n * m
commutative m zero 
  rewrite left-zero m = refl
commutative m (suc n)
  rewrite left-suc n m
  | Add.commutative (n * m) m = ap (m +_) (commutative m n)

{-
    suc m * (n + k)
  = (m * (n + k)) + n + k
  = (m * n + m * k) + n + k

    suc m * n + suc m * k
  = ((m * n) + n) + (m * k) + k
-}
distrib-+-left : (m n k : Nat) -> m * (n + k) ≡ m * n + m * k
distrib-+-left zero n k
  rewrite left-zero n
  | left-zero k
  | left-zero (n + k) = refl
distrib-+-left (suc m) n k
  rewrite left-suc m (n + k)
  | left-suc m n
  | left-suc m k
  | distrib-+-left m n k
  | Add.assoc (m * n) (m * k) (n + k)
  | inv (Add.assoc (m * k) n k) 
  | Add.commutative (m * k) n 
  | Add.assoc n (m * k) k
  | inv (Add.assoc (m * n) n (m * k + k)) = refl

{-
    (m + n) * suc k
  = (m + n) + ((m + n) * k)
  = (m + n) + (m * k + n * k)

    m * (suc k) + n * (suc k)
  = (m + m * k) + (n + n * k)
-}
distrib-+-right : (m n k : Nat) -> (m + n) * k ≡ m * k + n * k
distrib-+-right m n zero = refl
distrib-+-right m n (suc k)
  rewrite distrib-+-right m n k
  | Add.assoc m n (m * k + n * k)
  | inv (Add.assoc n (m * k) (n * k))
  | Add.commutative n (m * k)
  | Add.assoc (m * k) n (n * k)
  | inv (Add.assoc m (m * k) (n + n * k)) = refl
