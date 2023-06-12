open import Nat
open import Identity using (_≡_; ap)
open import Function using (_$_; _∘_)
open import Empty using (ex-falso; ¬_)

module Nat.Properties.Less where

not-n<0 : ∀ {n} -> ¬ (n < 0)
not-n<0 ()

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
asym : ∀ {m n} -> m < n -> ¬ (n < m)
asym (s<s m<n) (s<s n<m) = asym m<n n<m

-- asym-bck : ∀ {m n} -> ¬ (m < n) -> n < m
-- asym-bck {zero} {zero} = {!   !} -- ?
-- asym-bck {zero} {suc n} ¬0<s = ex-falso (¬0<s 0<s)
-- asym-bck {suc m} {zero} _ = 0<s
-- asym-bck {suc m} {suc n} ¬s<s = s<s $ asym-bck (¬s<s ∘ s<s)

