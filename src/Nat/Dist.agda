import Nat.Add as Add
import Nat.Mul as Mul
import Nat.Leq as Leq
import Nat.Less as Less
open import Nat.Base
open import Nat.Observational.Equality using (peano7-bck; peano8)
open import DependentPair using (_×_; _<-->_; _,_)
open import Coproduct using (_⨄_; inl; inr)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Identity using (_≡_; refl; inv; ap)

module Nat.Dist where

to-itself : ∀ n -> dist n n ≡ 0
to-itself zero = refl
to-itself (suc n) = to-itself n

right-unit : ∀ n -> dist n zero ≡ n
right-unit zero = refl
right-unit (suc n) = refl

{-
  Exercise 6.5.a.i
-}
itself-fwd : ∀ {m n} -> m ≡ n -> dist m n ≡ 0
itself-fwd {m} {_} refl = to-itself m

itself-bck : ∀ {m n} -> dist m n ≡ 0 -> m ≡ n
itself-bck {zero} {n} = inv
itself-bck {suc m} {zero} = id
itself-bck {suc m} {suc n} = ap suc ∘ itself-bck

itself : ∀ {m n} -> (m ≡ n) <--> (dist m n ≡ 0)
itself = itself-fwd , itself-bck

{-
  Exercise 6.5.a.ii
-}
commutative : ∀ m n -> dist m n ≡ dist n m
commutative zero n = inv (right-unit n)
commutative (suc m) zero = refl
commutative (suc m) (suc n) = commutative m n

{-
  Exercise 6.5.a.iii
-}
leq-add : ∀ m n -> dist m n ≤ m + n
leq-add zero n rewrite Add.left-unit n = Leq.reflex
leq-add (suc m) zero rewrite Add.left-unit m = Leq.reflex
leq-add (suc m) (suc n) rewrite Add.left-suc m n = Leq.right-suc $ Leq.right-suc (leq-add m n)

leq-dist-k : ∀ m n -> m ≤ dist m n + n
leq-dist-k zero n = 0≤n
leq-dist-k (suc m) zero = Leq.reflex
leq-dist-k (suc m) (suc n) = s≤s (leq-dist-k m n)

triangle : ∀ m n k -> dist m n ≤ dist m k + dist k n
triangle m n zero rewrite right-unit m = leq-add m n
triangle zero zero (suc k) = 0≤n
triangle zero (suc n) (suc k) rewrite Add.left-suc k (dist k n)
  | Add.commutative k (dist k n)
  | commutative k n = s≤s (leq-dist-k n k)
triangle (suc m) zero (suc k) = s≤s (leq-dist-k m k)
triangle (suc m) (suc n) (suc k) = triangle m n k

{-
  Exercise 6.5.b
-}
triangle-eq-fwd : ∀ m n k
  -> dist m n ≡ dist m k + dist k n
  -> ((m ≤ k) × (k ≤ n)) ⨄ ((n ≤ k) × (k ≤ m))
triangle-eq-fwd zero zero zero _ = inl (0≤n , 0≤n)
triangle-eq-fwd zero zero (suc k) eq = inl (0≤n , (ex-falso $ peano8 eq))
triangle-eq-fwd zero (suc n) zero _ = inl (0≤n , 0≤n)
triangle-eq-fwd zero (suc n) (suc k) eq rewrite Add.left-suc k (dist k n)
  with triangle-eq-fwd zero n k (peano7-bck eq)
... | inl (_ , k≤n) = inl (0≤n , s≤s k≤n)
... | inr (n≤k , k≤0) rewrite Leq.when-n≤0 k≤0 | Leq.when-n≤0 n≤k = inl (0≤n , s≤s 0≤n)
triangle-eq-fwd (suc m) zero zero _ = inr (0≤n , 0≤n)
triangle-eq-fwd (suc m) zero (suc k) eq = result where
  hyp : m ≡ dist m k + k -> dist m 0 ≡ dist m k + dist k 0
  hyp rewrite right-unit m | right-unit k = id

  result : ((suc m ≤ suc k) × (suc k ≤ zero)) ⨄ ((zero ≤ suc k) × (suc k ≤ suc m))
  result with triangle-eq-fwd m zero k (hyp $ peano7-bck eq)
  ... | inl (m≤k , k≤0) rewrite Leq.when-n≤0 k≤0 | Leq.when-n≤0 m≤k = inr (0≤n , s≤s 0≤n)
  ... | inr (_ , k≤m) = inr (0≤n , s≤s k≤m)
triangle-eq-fwd (suc m) (suc n) zero
  rewrite Add.left-suc m n = ex-falso ∘ Leq.ineq-+-nonzero {dist m n} {m + n} {1} (leq-add m n)
triangle-eq-fwd (suc m) (suc n) (suc k) eq with triangle-eq-fwd m n k eq
... | inl (m≤k , k≤n) = inl (s≤s m≤k , s≤s k≤n)
... | inr (n≤k , k≤m) = inr (s≤s n≤k , s≤s k≤m)

triangle-eq-bck : ∀ {m n k}
  -> ((m ≤ k) × (k ≤ n)) ⨄ ((n ≤ k) × (k ≤ m))
  -> dist m n ≡ dist m k + dist k n
triangle-eq-bck {_} {n} {_} (inl (0≤n , 0≤n)) = inv $ Add.left-unit n
triangle-eq-bck {_} {suc n} {suc k} (inl (0≤n , s≤s k≤n))
  rewrite Add.left-suc k (dist k n) = ap suc $ triangle-eq-bck $ inl (0≤n , k≤n)
triangle-eq-bck (inl (s≤s m≤k , s≤s k≤n)) = triangle-eq-bck $ inl (m≤k , k≤n)
triangle-eq-bck {m} {_} {_} (inr (0≤n , 0≤n)) rewrite right-unit m = refl
triangle-eq-bck {suc m} {_} {suc k} (inr (0≤n , s≤s k≤m)) = ap suc $ hyp $ triangle-eq-bck $ inr (0≤n , k≤m) where
  hyp : dist m 0 ≡ dist m k + dist k 0 -> m ≡ dist m k + k
  hyp rewrite right-unit m | right-unit k = id
triangle-eq-bck (inr (s≤s n≤k , s≤s k≤m)) = triangle-eq-bck $ inr (n≤k , k≤m)

triangle-eq : ∀ m n k
  -> (dist m n ≡ dist m k + dist k n) <--> (((m ≤ k) × (k ≤ n)) ⨄ ((n ≤ k) × (k ≤ m)))
triangle-eq m n k = triangle-eq-fwd m n k , triangle-eq-bck

{-
  Exercise 6.5.c.i
-}
invariant : ∀ k m n -> dist (k + m) (k + n) ≡ dist m n
invariant zero m n rewrite Add.left-unit m | Add.left-unit n = refl
invariant (suc k) m n rewrite Add.left-suc k m | Add.left-suc k n = invariant k m n

{-
  Exercise 6.5.c.ii
-}
linear : ∀ k m n -> dist (k * m) (k * n) ≡ k * dist m n
linear zero m n rewrite Mul.left-zero m | Mul.left-zero n = inv $ Mul.left-zero (dist m n)
linear (suc k) zero n = refl
linear (suc k) (suc m) zero = right-unit (suc k + suc k * m)
linear (suc k) (suc m) (suc n)
  rewrite invariant (suc k) (suc k * m) (suc k * n) = linear (suc k) m n

{-
  Exercise 6.5.d
-}
from-leq  : ∀ {m n} -> n ≤ m -> dist m n + n ≡ m
from-leq  {m} {_} 0≤n = right-unit m
from-leq  (s≤s n≤m) = ap suc (from-leq  n≤m)

from-less : ∀ {m n} -> n < m -> dist m n + n ≡ m
from-less 0<s = refl
from-less (s<s n<m) = ap suc (from-less n<m)

clear-add-eq-when-n≤m : ∀ m n k -> n ≤ m -> m ≡ n + k -> dist m n ≡ k
clear-add-eq-when-n≤m m zero k 0≤n
  rewrite Add.left-unit k | right-unit m = id
clear-add-eq-when-n≤m (suc m) (suc n) k (s≤s n≤m)
  rewrite Add.left-suc n k = clear-add-eq-when-n≤m m n k n≤m ∘ peano7-bck

clear-add-eq : ∀ m n k -> m ≡ n + k -> dist m n ≡ k
clear-add-eq m n k eq = clear-add-eq-when-n≤m m n k (Leq.leq-for-add-eq m n k eq) eq

dist-through-fwd : ∀ {m n k}
  -> m ≤ n
  -> n ≤ k
  -> dist m k ≡ dist m n + dist n k
dist-through-fwd m≤n n≤k = triangle-eq-bck $ inl (m≤n , n≤k)

dist-through-bck : ∀ {m n k}
  -> m ≤ n
  -> n ≤ k
  -> dist k m ≡ dist k n + dist n m
dist-through-bck m≤n n≤k = triangle-eq-bck $ inr (m≤n , n≤k)

both-less-than-k : ∀ {m n k}
  -> m < k
  -> n < k
  -> dist m n < k
both-less-than-k 0<s 0<s = 0<s
both-less-than-k 0<s (s<s n<k) = s<s n<k
both-less-than-k (s<s m<k) 0<s = s<s m<k
both-less-than-k (s<s m<k) (s<s n<k) = Less.right-suc (both-less-than-k m<k n<k)
