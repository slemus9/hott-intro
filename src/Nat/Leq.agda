import Nat.Add as Add
open import Nat.Observational.Equality using (peano7-bck; peano8)
open import Nat.Base
open import Empty using (ex-falso)
open import Empty.Negation using (¬_)
open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (_<-->_; _×_; _,_)
open import Function using (id; _∘_)
open import Identity using (_≢_; _≡_; refl; ap)

module Nat.Leq where

not-s≤0 : ∀ {n} -> ¬ (suc n ≤ 0)
not-s≤0 {zero} ()

right-suc : ∀ {m n} -> m ≤ n -> m ≤ suc n
right-suc 0≤n = 0≤n
right-suc (s≤s m≤n) = s≤s (right-suc m≤n)

when-n≤0  : ∀ {n} -> n ≤ 0 -> n ≡ 0
when-n≤0  0≤n = refl

when-m≤sn : ∀ {m n} -> m ≤ suc n -> (m ≡ suc n) ⨄ (m ≤ n)
when-m≤sn {zero} {n} 0≤n = inr 0≤n
when-m≤sn {suc m} {zero} (s≤s m≤0) rewrite when-n≤0 m≤0 = inl refl
when-m≤sn {suc m} {suc n} (s≤s m≤sn) with when-m≤sn m≤sn
... | inl m≡sn = inl (ap suc m≡sn)
... | inr m≤n = inr (s≤s m≤n)

n<=n+m : ∀ {n m} -> n ≤ n + m
n<=n+m {zero} {m} = 0≤n
n<=n+m {suc n} {m} rewrite Add.left-suc n m = s≤s n<=n+m

ineq-+-nonzero : ∀ {m n k} -> m ≤ n -> m ≢ n + (k + 1)
ineq-+-nonzero {suc m} {suc n} {k} (s≤s m≤n)
  rewrite Add.left-suc n k = ineq-+-nonzero m≤n ∘ peano7-bck

{-
  Exercise 6.3.a.i
-}
reflex : ∀ {n} -> n ≤ n
reflex {zero} = 0≤n
reflex {suc n} = s≤s reflex

{-
  Exercise 6.3.a.ii
-}
antisym : ∀ {m n} -> m ≤ n -> n ≤ m -> n ≡ m
antisym 0≤n 0≤n = refl
antisym (s≤s m≤n) (s≤s n≤m) = ap suc (antisym m≤n n≤m)

{-
  Exercise 6.3.a.iii
-}
trans : ∀ {m n k} -> m ≤ n -> n ≤ k -> m ≤ k
trans 0≤n _ = 0≤n
trans (s≤s m≤n) (s≤s n≤k) = s≤s (trans m≤n n≤k)

{-
  Exercise 6.3.b
-}
total : ∀ m n -> (m ≤ n) ⨄ (n ≤ m)
total zero _ = inl 0≤n
total (suc m) zero = inr 0≤n
total (suc m) (suc n) with total m n
... | inl m≤n = inl (s≤s m≤n)
... | inr n≤m = inr (s≤s n≤m)

{-
  Exercise 6.3.c
-}
add-k-r-fwd : ∀ m n k -> m ≤ n -> m + k ≤ n + k
add-k-r-fwd _ _ zero = id
add-k-r-fwd m n (suc k) m≤n = s≤s (add-k-r-fwd m n k m≤n)

add-k-bck : ∀ m n k -> m + k ≤ n + k -> m ≤ n
add-k-bck _ _ zero = id
add-k-bck m n (suc k) (s≤s h) = add-k-bck m n k h

add-k : ∀ m n k -> (m ≤ n) <--> (m + k ≤ n + k)
add-k m n k = add-k-r-fwd m n k , add-k-bck m n k

{-
  Exercise 6.3.d
-}
add-k-l-fwd : ∀ k m n -> m ≤ n -> k + m ≤ k + n
add-k-l-fwd k m n
  rewrite Add.commutative k m | Add.commutative k n = add-k-r-fwd m n k

add-mono : ∀ m n p q -> m ≤ n -> p ≤ q -> m + p ≤ n + q
add-mono m n p q m≤n p≤q = trans (add-k-r-fwd m n p m≤n) (add-k-l-fwd n p q p≤q)

mul-nonzero : ∀ m n k -> m ≤ n -> m * (k + 1) ≤ n * (k + 1)
mul-nonzero m n zero = id
mul-nonzero m n (suc k) m≤n =
  add-mono m n (m * (k + 1)) (n * (k + 1)) m≤n (mul-nonzero m n k m≤n)

{-
  Exercise 6.3.e.i
-}
leq-min-fwd : ∀ k m n -> k ≤ min m n -> (k ≤ m) × (k ≤ n)
leq-min-fwd zero m n _ = 0≤n , 0≤n
leq-min-fwd (suc k) zero n = ex-falso ∘ not-s≤0
leq-min-fwd (suc k) (suc m) zero = ex-falso ∘ not-s≤0
leq-min-fwd (suc k) (suc m) (suc n) (s≤s k≤min) with leq-min-fwd k m n k≤min
... | (k≤m , k≤n) = s≤s k≤m , s≤s k≤n

leq-min-bck : ∀ k m n -> (k ≤ m) × (k ≤ n) -> k ≤ min m n
leq-min-bck _ m n (0≤n , _) = 0≤n
leq-min-bck (suc k) (suc m) (suc n) (s≤s k≤m , s≤s k≤n) = s≤s (leq-min-bck k m n (k≤m , k≤n))

leq-min : ∀ k m n -> (k ≤ min m n) <--> ((k ≤ m) × (k ≤ n))
leq-min k m n = leq-min-fwd k m n , leq-min-bck k m n

{-
  Exercise 6.3.e.ii
-}
leq-max-fwd : ∀ m n k -> max m n ≤ k -> (m ≤ k) × (n ≤ k)
leq-max-fwd zero zero k _ = 0≤n , 0≤n
leq-max-fwd zero (suc n) k s≤k = 0≤n , s≤k
leq-max-fwd (suc m) zero k s≤k = s≤k , 0≤n
leq-max-fwd (suc m) (suc n) (suc k) (s≤s max≤k) with leq-max-fwd m n k max≤k
... | (m≤k , n≤k)  = s≤s m≤k , s≤s n≤k

leq-max-bck : ∀ m n k -> (m ≤ k) × (n ≤ k) -> max m n ≤ k
leq-max-bck zero n k (0≤n , n≤k) = n≤k
leq-max-bck (suc m) zero (suc k) (s≤s m≤k , 0≤n) = s≤s m≤k
leq-max-bck (suc m) (suc n) (suc k) (s≤s m≤k , s≤s n≤k) = s≤s (leq-max-bck m n k (m≤k , n≤k))

leq-max : ∀ m n k -> (max m n ≤ k) <--> ((m ≤ k) × (n ≤ k))
leq-max m n k = leq-max-fwd m n k , leq-max-bck m n k

leq-for-add-eq : ∀ m n k -> m ≡ n + k -> n ≤ m
leq-for-add-eq m zero k _ = 0≤n
leq-for-add-eq zero (suc n) k rewrite Add.left-suc n k = ex-falso ∘ peano8
leq-for-add-eq (suc m) (suc n) k
  rewrite Add.left-suc n k = s≤s ∘ leq-for-add-eq m n k ∘ peano7-bck
