import Nat.Divides as Div
import Nat.Leq as Leq
import Nat.Mul as Mul
open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (_,_)
open import Identity using (_≢_; _≡_; refl)
open import Nat.Base
open import Empty using (ex-falso)

module Nat.Factorial where

x-divides-x! : ∀ x -> x ≢ 0 -> x divides (x !)
x-divides-x! zero x≢0 = ex-falso (x≢0 refl)
x-divides-x! (suc x) _ = (x !) , refl

x-divides-sx! : ∀ x -> (x !) divides ((suc x) !)
x-divides-sx! zero = Div.one-divides-any 1
x-divides-sx! (suc x) rewrite Mul.commutative (suc (suc x)) ((suc x) !) = (suc (suc x)) , refl

{-
  x ≤ suc n => x ≡ suc n ⨄ x ≤ n

  if x ≡ suc n then
    x! divides (suc n)!

  if x ≤ n then
    Goal: x! divides (suc n)!
    IH: x! divides n!
    x! divides n! and n! divides (suc n)! then x! divides (suc n)!
-}
x≤n-x!-divides-n! : ∀ x n
  -> x ≤ n
  -> (x !) divides (n !)
x≤n-x!-divides-n! zero zero 0≤n = Div.one-divides-any 1
x≤n-x!-divides-n! x (suc n) x≤sn with Leq.when-m≤sn x≤sn
... | inl x≡sn rewrite x≡sn = 1 , refl
... | inr x≤n =
    Div.trans (x !) (n !) ((suc n) !)
      (x≤n-x!-divides-n! x n x≤n)
      (x-divides-sx! n)

{-
  Exercise 7.3
-}
x≤n-x-divides-n! : ∀ x n
  -> x ≢ 0
  -> x ≤ n
  -> x divides (n !)
x≤n-x-divides-n! x n x≢0 x≤n =
  Div.trans x (x !) (n !) (x-divides-x! x x≢0) (x≤n-x!-divides-n! x n x≤n)
