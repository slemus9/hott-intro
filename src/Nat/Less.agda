open import Nat.Base
import Nat.Leq as Leq
open import Identity using (_≡_; ap)
open import Function using (_$_; _∘_)
open import Empty using (ex-falso)
open import Empty.Negation using (¬_)

module Nat.Less where

not-n<0 : ∀ {n} -> ¬ (n < 0)
not-n<0 ()

asym : ∀ {m n} -> m < n -> ¬ (n < m)
asym (s<s m<n) (s<s n<m) = asym m<n n<m

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

{-
  Exercise 6.4.b
-}
right-suc : ∀ {m n} -> m < n -> m < n + 1
right-suc 0<s = 0<s
right-suc (s<s m<n) = s<s (right-suc m<n)

{-
  Exercise 6.4.c.i
-}
to-leq : ∀ {m n} -> m < n -> m + 1 ≤ n
to-leq 0<s = s≤s 0≤n
to-leq (s<s m<n) = s≤s (to-leq m<n)

{-
  Exercise 6.4.c.ii
-}
not-leq-fwd : ∀ {m n} -> m < n -> ¬ (n ≤ m)
not-leq-fwd 0<s = Leq.not-s≤0
not-leq-fwd (s<s m<n) (s≤s n≤m) = not-leq-fwd m<n n≤m

not-leq-bck : ∀ {m n} -> ¬ (m ≤ n) -> n < m
not-leq-bck {zero} {n} ¬0≤n = ex-falso (¬0≤n 0≤n)
not-leq-bck {suc m} {zero} _ = 0<s
not-leq-bck {suc m} {suc n} ¬sm≤sn = s<s $ not-leq-bck (¬sm≤sn ∘ s≤s)

n<s : ∀ {n} -> n < suc n
n<s {zero} = 0<s
n<s {suc n} = s<s n<s

when-equal : ∀ {m n} -> m ≡ n -> ¬ (m < n)
when-equal eq rewrite eq = antireflex
