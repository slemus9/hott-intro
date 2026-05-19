open import Fin.Base
open import Nat.Base
open import Nat.Division
open import Type
open import Empty
open import Empty.Negation
open import DependentPair

module Fin.NatK.Base where

data ℕ : Nat -> Type where
  constant : ∀ {k} -> Fin k -> ℕ k
  unary : ∀ {k} -> Fin k -> ℕ k -> ℕ k

to-nat : ∀ {k} -> ℕ k -> Nat
to-nat (constant x) = incl x
to-nat {k} (unary x n) = k * (to-nat n + 1) + incl x

{-
  Exercise 7.10.a
-}
empty-ℕ₀ : is-empty (ℕ 0)
empty-ℕ₀ (constant ())
empty-ℕ₀ (unary () _)

-- Observational Equality
Eq-ℕ : ∀ {k} -> ℕ k -> ℕ k -> Type
Eq-ℕ (constant x) (constant y) = Eq-Fin x y
Eq-ℕ (constant _) (unary _ _) = Empty
Eq-ℕ (unary _ _) (constant _) = Empty
Eq-ℕ (unary x n) (unary y m) = (Eq-Fin x y)  × (Eq-ℕ n m)

zero-ℕ : ∀ {k} -> ℕ (suc k)
zero-ℕ = constant zero-fin

{-
  Exercise 7.10.c.i

  So that I don't forget in the future:

  The way I thought about this function (and how it interacts with from-nat), was basically by enumerating
  all mappings from Nat to ℕ k, from the perspective of the following to-nat definition:

  to-natₖ(ℕₖ(x₁, x₂, ..., xₘ)) = incl(x₁) + k * incl(x₂) + k^2 * incl(x₃) + ... + k^(m - 1) * incl(xₘ)

  where:

  ℕₖ(x₁, x₂, ..., xₘ) = unary(x₁, unary(x₂, unary(..., constant(xₘ))))

  Each incl(xᵢ) can have at most k possible values (from 0 to k - 1).
    
  This way, it was easier for me to think about which n:ℕₖ would generate a given a:Nat starting from 0. For example, if k = 4,
  then the first 4 ℕₖ values are these:

  a = 0 ---> n = constant (i (i (i (base {0}))))
  a = 1 ---> n = constant (i (i (base {1})))
  a = 2 ---> n = constant (i (base {2}))
  a = 3 ---> n = constant (base {3})

  because for a < k, incl [ a ] = a (This case is represented by the first base case in the suc-ℕ formula).
  
  Then, to generate a = 4, we can see that the only way to do it is like this (This is the second base case of the suc-ℕ formula):

  a = 4 
    = to-nat(unary(zero-fin, zero-ℕ)) 
    = incl(zero-fin) + 4 * (incl(zero-ℕ) + 1) 
    = 0 + 4 * (0 + 1)

  Then we notice that in order to generate a = {4 ... 7}, we only need to increase incl(x₁) and keep x₂ as is:

  a = 5 = 1 + 4 * (0 + 1)
  a = 6 = 2 + 4 * (0 + 1)
  a = 7 = 3 + 4 * (0 + 1)

  When we reach a = 8, the way to get that term is by increasing incl(x₂) by one, and leave incl(x₁) as zero:

  a = 8 = 0 + 4 * (1 + 1)

  We can now see a pattern. To generate a = {9 ... 11}, we need to increase incl(x₁) and keep x₂ as is:

  a = 9 = 1 + 4 * (1 + 1)
  a = 10 = 2 + 4 * (1 + 1)
  a = 11 = 3 + 4 * (1 + 1)

  When we get to a = 19 = 3 + 4 * (3 + 1), we need a new term in the to-nat summation; that is, we need to add another unary constructor so that we can use the 4^2 term:

  a = 20 = 0 + 4 * (0 + 1) + 4^2 * (0 + 1)

  We then repeat the same process recursively and iterate between all combinations of x₁ and x₂ to generate all numbers until 83, 
  by which point we will need to add another unary constructor to gain access to the 4^3 term and build 84
-}
suc-ℕ : ∀ {k} -> ℕ k -> ℕ k
suc-ℕ (constant (i x)) = constant (suc-fin (i x))
suc-ℕ (constant base) = unary zero-fin zero-ℕ
suc-ℕ (unary (i x) n) = unary (suc-fin (i x)) n 
suc-ℕ (unary base n) = unary zero-fin (suc-ℕ n)


from-nat : ∀ {k} -> Nat -> ℕ (suc k)
from-nat zero = zero-ℕ
from-nat (suc a) = suc-ℕ (from-nat a)
