import Nat.Properties.Add as Add
import Nat.Properties.Leq as Leq
open import Nat
open import DependentPair using (_<-->_; _,_)
open import Function using (id; _∘_; _$_)
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
leq-add (suc m) (suc n) rewrite Add.left-suc m n = Leq.left-suc $ Leq.left-suc (leq-add m n) 

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
