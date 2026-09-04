open import Nat.Base
import Nat.Leq as Leq
import Nat.Add as Add
import Nat.Observational.Equality as NatEq
open import Identity using (_≢_; _≡_; refl; inv; ap; tr)
open import Function using (_$_; _∘_)
open import Empty using (ex-falso)
open import Empty.Negation using (¬_)
open import Type using (Type)
open import Coproduct

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

from-leq : ∀ {m n} -> m ≤ n -> m < n + 1
from-leq 0≤n = 0<s
from-leq (s≤s l) = s<s (from-leq l)

from-leq-pred : ∀ {m n} -> suc m ≤ n -> m < n
from-leq-pred (s≤s leq) = from-leq leq

trans-suc : ∀ {m n k} -> m < n -> n < k -> suc m < k
trans-suc {m} {n} {k} m-less-n n-less-k with Leq.to-less-or-equal (to-leq m-less-n)
-- when suc m ≡ n
... | inl sm-eq-n = tr {Nat} {_< k} {n} {suc m} (inv sm-eq-n) n-less-k
-- when suc m < n
... | inr sm-less-n = trans sm-less-n n-less-k

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

not-eq : ∀ {m n} -> m < n -> m ≢ n
not-eq 0<s = NatEq.peano8
not-eq (s<s l) = not-eq l ∘ NatEq.peano7-bck

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

when-not-zero-fwd : ∀ {n} -> n ≢ 0 -> 0 < n
when-not-zero-fwd {zero} n≢0 = ex-falso (n≢0 refl)
when-not-zero-fwd {suc n} _ = 0<s

when-not-zero-bck : ∀ {n} -> 0 < n -> n ≢ 0
when-not-zero-bck 0<s = NatEq.peano8 ∘ inv

not-less-than-zero : ∀ {n} -> ¬ (n < zero)
not-less-than-zero {zero} = antireflex
not-less-than-zero {suc n} = asym 0<s

not-s<n : ∀ {n} -> ¬ (suc n < n)
not-s<n (s<s s<n) = not-s<n s<n

not-n+m<n : ∀ {n m} -> ¬ (n + m < n)
not-n+m<n {n} {zero} = antireflex
not-n+m<n {zero} {suc m} rewrite Add.left-unit m = not-n<0
not-n+m<n {suc n} {suc m} (s<s l) rewrite Add.associative n 1 m = not-n+m<n {n} {1 + m} l

leq-to-not-less : ∀ {n m} -> n ≤ m -> ¬ (m < n)
leq-to-not-less 0≤n = not-less-than-zero
leq-to-not-less (s≤s n≤m) (s<s m<n) = ex-falso (leq-to-not-less n≤m m<n)

not-suc : ∀ {n m} -> ¬ (suc n < suc m) -> ¬ (n < m)
not-suc {_} {zero} _ = not-less-than-zero
not-suc {zero} {suc m} notLessSuc = ex-falso $ notLessSuc $ s<s 0<s
not-suc {suc n} {suc m} notLessSuc sn<sm = ex-falso $ notLessSuc $ s<s sn<sm

not-less-to-leq : ∀ {n m} -> ¬ (n < m) -> m ≤ n
not-less-to-leq {n} {zero} notLess = 0≤n
not-less-to-leq {zero} {suc m} notLess = ex-falso (notLess 0<s)
not-less-to-leq {suc n} {suc m} notLess = s≤s $ not-less-to-leq $ not-suc notLess

less-suc-to-leq : ∀ {n m} -> n < suc m -> (n < m) ⨄ (n ≡ m)
less-suc-to-leq {_} {zero} 0<s = inr refl
less-suc-to-leq {_} {suc m} 0<s = inl 0<s
less-suc-to-leq {suc n} {suc m} (s<s l) with less-suc-to-leq l 
... | inl l = inl (s<s l)
... | inr eq = inr (ap suc eq)

non-zero-addition : ∀ {n m} -> 0 < m -> 0 < n + m
non-zero-addition 0<s = 0<s
