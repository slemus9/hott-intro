import Nat.Properties.Add as Add
import Nat.Properties.Leq as Leq
open import Nat.Properties.Observational.Equality using (peano7-r; peano8)
open import Nat
open import DependentPair using (_×_; _<-->_; _,_)
open import Coproduct using (_⨄_; inl; inr)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Identity using (_≡_; refl; inv; ap)

module Nat.Properties.Dist where

to-itself : ∀ n -> dist n n ≡ 0
to-itself zero = refl
to-itself (suc n) = to-itself n

right-unit : ∀ n -> dist n zero ≡ n
right-unit zero = refl
right-unit (suc n) = refl

{-
  Exercise 6.5.a.i
-}
itself-fwd : ∀ m n -> m ≡ n -> dist m n ≡ 0
itself-fwd m n refl = to-itself m

itself-bck : ∀ m n -> dist m n ≡ 0 -> m ≡ n
itself-bck zero n = inv
itself-bck (suc m) zero = id
itself-bck (suc m) (suc n) = ap suc ∘ itself-bck m n

itself : ∀ m n -> (m ≡ n) <--> (dist m n ≡ 0)
itself m n = itself-fwd m n , itself-bck m n

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
  with triangle-eq-fwd zero n k (peano7-r eq)
... | inl (_ , k≤n) = inl (0≤n , s≤s k≤n)
... | inr (n≤k , k≤0) rewrite Leq.n≤0 k≤0 | Leq.n≤0 n≤k = inl (0≤n , s≤s 0≤n)
triangle-eq-fwd (suc m) zero zero _ = inr (0≤n , 0≤n)
triangle-eq-fwd (suc m) zero (suc k) eq = result where
  hyp : m ≡ dist m k + k -> dist m 0 ≡ dist m k + dist k 0
  hyp rewrite right-unit m | right-unit k = id

  result : ((suc m ≤ suc k) × (suc k ≤ zero)) ⨄ ((zero ≤ suc k) × (suc k ≤ suc m))
  result with triangle-eq-fwd m zero k (hyp $ peano7-r eq)
  ... | inl (m≤k , k≤0) rewrite Leq.n≤0 k≤0 | Leq.n≤0 m≤k = inr (0≤n , s≤s 0≤n)
  ... | inr (_ , k≤m) = inr (0≤n , s≤s k≤m)
triangle-eq-fwd (suc m) (suc n) zero
  rewrite Add.left-suc m n = ex-falso ∘ Leq.ineq-+-nonzero {dist m n} {m + n} {1} (leq-add m n)
triangle-eq-fwd (suc m) (suc n) (suc k) eq with triangle-eq-fwd m n k eq
... | inl (m≤k , k≤n) = inl (s≤s m≤k , s≤s k≤n)
... | inr (n≤k , k≤m) = inr (s≤s n≤k , s≤s k≤m)
