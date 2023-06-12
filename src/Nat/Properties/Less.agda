open import Nat
open import Identity using (_≡_; ap)
open import Empty using (¬_)

module Nat.Properties.Less where

{-
  Exercise 6.4.a.i
-}
antireflex : ∀ {n} -> ¬ (n < n)
antireflex (s<s n<n) = antireflex n<n

{-
  Exercise 6.4.a.ii
-}
antisym : ∀ {m n} -> m < n -> n < m -> m ≡ n
antisym (s<s m<n) (s<s n<m) = ap suc (antisym m<n n<m)

{-
  Exercise 6.4.a.iii
-}
trans : ∀ {m n k} -> m < n -> n < k -> m < k
trans 0<s (s<s _) = 0<s
trans (s<s m<n) (s<s n<k) = s<s (trans m<n n<k)


asym : ∀ {m n} -> m < n -> ¬ (n < m)
asym (s<s m<n) (s<s n<m) = asym m<n n<m