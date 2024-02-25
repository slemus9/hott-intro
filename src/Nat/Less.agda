open import Nat.Base
import Nat.Leq as Leq
open import Identity using (_≢_; _≡_; refl; ap)
open import Function using (_$_; _∘_)
open import Empty using (ex-falso)
open import Empty.Negation using (¬_)
open import Type using (Type)

module Nat.Less where

data Connected (m n : Nat) : Type where
  low : m < n -> Connected m n
  middle : m ≡ n -> Connected m n
  high : n < m -> Connected m n

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

<-uniq : ∀ {x y} -> (p1 p2 : x < y) -> p1 ≡ p2
<-uniq 0<s 0<s = refl
<-uniq (s<s p1) (s<s p2) = ap s<s (<-uniq p1 p2)

connected : ∀ m n -> Connected m n
connected zero zero = Connected.middle refl
connected zero (suc _) = Connected.low 0<s
connected (suc m) zero = Connected.high 0<s
connected (suc m) (suc n) with connected m n
... | low m<n = Connected.low (s<s m<n)
... | middle m≡n = Connected.middle (ap suc m≡n)
... | high n<m = Connected.high (s<s n<m)

when-not-zero : ∀ {n} -> n ≢ 0 -> 0 < n
when-not-zero {zero} n≢0 = ex-falso (n≢0 refl)
when-not-zero {suc n} _ = 0<s
