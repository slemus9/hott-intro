import DependentPair.Identification as DP
open import DependentPair using (_<-->_; _,_; fst)
open import Fin.Base
open import Identity using (_≡_; refl; ap)
open import Nat using (Nat; _<_)
open import Nat.Less using (<-uniq)

module Fin.Classical where

eq-fst-fwd : ∀ {k} -> (x y : ClassicalFin k) -> x ≡ y -> fst x ≡ fst y
eq-fst-fwd _ _ = ap fst

eq-fst-bck : ∀ {k} -> (x y : ClassicalFin k) -> fst x ≡ fst y -> x ≡ y
eq-fst-bck {k} (a1 , b1) (a2 , b2) eq with DP.eq-fst {Nat} {_< k} a1 a2 b1 b2 eq
... | refl rewrite (<-uniq b1 b2) = refl

{-
  Exercise 7.7.a
-}
eq-fst : ∀ {k} -> (x y : ClassicalFin k) -> (x ≡ y) <--> (fst x ≡ fst y)
eq-fst x y = eq-fst-fwd x y , eq-fst-bck x y
