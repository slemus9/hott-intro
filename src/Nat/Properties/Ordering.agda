open import Nat using (Nat; zero; suc; _≤_; 0≤n; s≤s)
open import Empty using (¬_)
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
