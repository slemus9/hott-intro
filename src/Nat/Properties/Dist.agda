open import Nat
open import DependentPair using (_<-->_; _,_)
open import Function using (id; _∘_)
open import Identity using (_≡_; refl; inv; ap)

module Nat.Properties.Dist where

to-itself : ∀ n -> dist n n ≡ 0
to-itself zero = refl
to-itself (suc n) = to-itself n

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
