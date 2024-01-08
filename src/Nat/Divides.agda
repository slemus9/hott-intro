open import Function using (_$_)
open import Nat.Base
import Nat.Add as Add
import Nat.Leq as Leq
import Nat.Less as Less
import Nat.Mul as Mul
import Nat.Dist as Dist
open import DependentPair using (_,_; _×_; snd)
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning
open import Empty using (ex-falso)

module Nat.Divides where

one-divides-any : ∀ n -> 1 divides n
one-divides-any n = n , Mul.left-unit n

any-divides-zero : ∀ n -> n divides 0
any-divides-zero n = 0 , refl

zero-divides-zero : ∀ n -> 0 divides n -> n ≡ 0
zero-divides-zero n (k , 0*k≡n) =
  begin
    n
  ≡⟨ inv 0*k≡n ⟩
    0 * k
  ≡⟨ Mul.left-zero k ⟩
    0
  ∎

{-
  Exercise 7.2
-}
reflex : ∀ n -> n divides n
reflex n = 1 , refl

{-
  Goal: suc m = n

  Givens:
    suc m * k1 = n
    n * k2 = suc m
  ==> (suc m * k1) * k2  = suc m
  ==> suc m * (k1 * k2) = suc m
  ==> k1 * k2 = 1
  ==> k1 = 1, k2 = 1

      suc m * k1 = n
  ==> suc m * 1 = n
-}
antisym : ∀ m n -> m divides n -> n divides m -> m ≡ n
antisym zero n 0|n _  = inv $ zero-divides-zero n 0|n
antisym (suc m) n (k1 , sm*k1≡n) (k2 , n*k2≡sm) =
  begin
    suc m
  ≡⟨ inv n*k2≡sm ⟩
    n * k2
  ≡⟨ ap (n *_) (snd k1*k2≡1) ⟩
    n
  ∎ where
  sm*k1*k2≡sm : suc m * (k1 * k2) ≡ suc m
  sm*k1*k2≡sm rewrite inv $ Mul.assoc (suc m) k1 k2 | sm*k1≡n = n*k2≡sm

  k1*k2≡1 : (k1 ≡ 1) × (k2 ≡ 1)
  k1*k2≡1 = Mul.both-one-fwd $ Mul.eq-mul-one sm*k1*k2≡sm

{-
  Goal: m * k3 = k

  Givens
    m * k1 = n
    n * k2 = k
  ==> (m * k1) * k2 = k
  ==> m * (k1 * k2) = k
  ==> k3 = k1 * k2
-}
trans : ∀ m n k -> m divides n -> n divides k -> m divides k
trans m n k (k1 , m*k1≡n) (k2 , n*k2≡k) = (k1 * k2) , m*k3≡k where
  m*k3≡k : m * (k1 * k2) ≡ k
  m*k3≡k rewrite inv $ Mul.assoc m k1 k2 | m*k1≡n  = n*k2≡k


divides-x-y-then-x+y : ∀ d x y
  -> d divides x
  -> d divides y
  -> d divides (x + y)
divides-x-y-then-x+y d x y (k1 , d*k1≡x) (k2 , d*k2≡y)
  rewrite (inv d*k1≡x) | (inv d*k2≡y) = (k1 + k2) , Mul.distrib-+-left d k1 k2

{-
  Exercise 7.1

  d * k1 = x
  d * k2 = x + y
    => d * k2 = d * k1 + y
    => dist (d * k2) (d * k1) = y
    => d * dist k2 k1 = y
-}
divides-x-x+y-then-y : ∀ d x y
  -> d divides x
  -> d divides (x + y)
  -> d divides y
divides-x-x+y-then-y d x y (k1 , d*k1≡x) (k2 , d*k2≡x+y)
  rewrite (inv d*k1≡x) = dist k2 k1 , d*k3≡y where
    d*k3≡y : d * dist k2 k1 ≡ y
    d*k3≡y =
      begin
        d * dist k2 k1
      ≡⟨ inv (Dist.linear d k2 k1) ⟩
        dist (d * k2) (d * k1)
      ≡⟨ Dist.clear-add-eq (d * k2) (d * k1) y d*k2≡x+y ⟩
        y
      ∎

divides-y-x+y-then-y : ∀ d x y
  -> d divides y
  -> d divides (x + y)
  -> d divides x
divides-y-x+y-then-y d x y
  rewrite Add.commutative x y = divides-x-x+y-then-y d y x

{-
  Case: x = 0
    Goal: x = 0
    x = 0

  Case: x = suc x
    Goal: suc x = 0

    Givens:
      suc x < d => ¬ (d ≤ suc x)
      d divides (suc x) => d * k = suc x

    Case: k = 0
      d * k = suc x => 0 = suc x (contradiction)

    Case: k = suc k
      Givens:
        d * suc k = suc x
        d ≤ d * suc k

      d ≤ suc x (contradiction)
-}
divisor-less-than-dividend-fwd : ∀ {d x}
  -> x < d
  -> d divides x
  -> x ≡ 0
divisor-less-than-dividend-fwd {_} {zero} _ _ = refl
divisor-less-than-dividend-fwd {d} {suc x} x+1<d (suc k , d+d*k≡x+1) = ex-falso $ Less.not-leq-fwd x+1<d d≤x+1 where
  d≤x+1 : d ≤ suc x
  d≤x+1 rewrite (inv d+d*k≡x+1) = Leq.n<=n+m

divisor-less-than-dividend-bck : ∀ {d x}
  -> x < d
  -> x ≡ 0
  -> d divides x
divisor-less-than-dividend-bck {d} {_} _ refl = any-divides-zero d
