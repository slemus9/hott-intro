open import Type using (Type)
open import Nat using (Nat; zero; suc; ind-nat; _+_)
open import Nat.Properties.Observational.Equality using (peano7; peano8)
open import Identity using (_≡_; refl; ap; trans; inv)
open import DependentPair using (_×_; _<-->_; _,_; snd)
open import Function using (id; _$_)
open import Empty using (ex-falso)

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

{-
  Exercise 6.1.a.i
-}
add-k : {m n k : Nat} -> (m ≡ n) <--> (m + k ≡ n + k)
add-k {m} {n} {k} = to m n k , from m n k where
  to : ∀ m n k -> m ≡ n -> m + k ≡ n + k
  to m n zero = id
  to m n (suc k) m≡n rewrite m≡n = refl

  from : ∀ m n k -> m + k ≡ n + k -> m ≡ n
  from m n zero = id
  from m n (suc k) eq = from m n k (snd peano7 eq)

{-
  Exercise 6.1.b.i
-}
both-zero : {m n : Nat} -> (m + n ≡ 0) <--> ((m ≡ 0) × (n ≡ 0))
both-zero {m} {n} = to m n , from where
  to : ∀ m n ->  m + n ≡ 0 -> (m ≡ 0) × (n ≡ 0)
  to zero n eq = refl , trans (inv $ left-unit n) eq
  to m zero eq = eq , refl
  to (suc m) (suc n) eq = (ex-falso $ peano8 $ inv eq) , (ex-falso $ peano8 $ inv eq) 

  from : (m ≡ 0) × (n ≡ 0) -> m + n ≡ 0
  from (refl , refl) = refl
