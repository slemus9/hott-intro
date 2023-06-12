import Nat.Properties.Add as Add
open import Nat
open import Empty using (¬_; ex-falso)
open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (_<-->_; _×_; _,_)
open import Function using (id; _∘_)
open import Identity using (_≢_; _≡_; refl; ap)

module Nat.Properties.Ordering where

not-s≤0 : ∀ {n} -> ¬ (suc n ≤ 0)
not-s≤0 {zero} ()

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
total : ∀ {m n} -> (m ≤ n) ⨄ (n ≤ m)
total {zero} {_} = inl 0≤n
total {suc m} {zero} = inr 0≤n
total {suc m} {suc n} with total {m} {n} 
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
... | (k≤m , k≤n)  = s≤s k≤m , s≤s k≤n
