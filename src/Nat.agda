open import Type using (Type)

module Nat where

-- Data Types
data Nat : Type where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data _≤_ : Nat -> Nat -> Type where
  0≤n : ∀ {n} -> zero ≤ n
  s≤s : ∀ {m n} -> m ≤ n -> suc m ≤ suc n

infix 4 _≤_

-- Operations
{-
  Induction principle:
  Ctx, x : Nat |- P x type
            Ctx |- p0 : P zero
            Ctx |- ps : (n : Nat) -> P n -> P (suc n)
  --------------------------------------------------
  Ctx, x : Nat |- ind(p0, ps, x) : (n : Nat) -> P x

  Computation rules: 
  Ctx, x : Nat |- P x type 
            Ctx |- p0 : P zero
            Ctx |- ps : (n : Nat) -> P n -> P (suc n)
  --------------------------------------------------
  Ctx |- ind(p0, ps, zero) = p0 : P zero

  Ctx, x : Nat |- P x type
            Ctx |- p0 : P zero
            Ctx |- ps : (n : Nat) -> P n -> P (suc n)
  --------------------------------------------------
  Ctx n : Nat |- ind(p0, ps, n) = ps(n, ind(p0, ps, n)) : P (suc n)
-}
ind-nat : {P : Nat -> Type}
  -> (p0 : P zero)
  -> (ps : (n : Nat) -> P n -> P (suc n))
  -> (n : Nat) -> P n
ind-nat p0 _ zero = p0
ind-nat p0 ps (suc n) = ps n (ind-nat p0 ps n)

-- Addition
_+_ : Nat -> Nat -> Nat
m + zero = m
m + suc n = suc (m + n)

-- Multiplication
_*_ : Nat -> Nat -> Nat
m * zero = zero
m * suc n = m + (m * n)

infixl 6  _+_
infixl 7  _*_

-- Exponentiation
_^_ : Nat -> Nat -> Nat
m ^ zero = 1
m ^ suc n = m * (m ^ n)

-- Minimum
min : Nat -> Nat -> Nat
min m zero = zero
min zero n = zero
min (suc m) (suc n) = suc (min m n)

-- Maximum
max : Nat -> Nat -> Nat
max m zero = m
max zero n = n
max (suc m) (suc n) = suc (max m n)

-- Triangular numbers
triangular : Nat -> Nat
triangular zero = zero
triangular (suc n) = (suc n) + triangular n

-- Factorial
_! : Nat -> Nat
zero ! = 1
(suc n) ! = suc n * (n !)

fact : Nat -> Nat
fact = _!

-- Binomial coefficient
bin-coef : Nat -> Nat -> Nat
bin-coef zero zero = 1
bin-coef zero (suc k) = zero
bin-coef (suc n) zero = 1
bin-coef (suc n) (suc k) = (bin-coef n k) + (bin-coef n (suc k))

-- Fibonacci
fib : Nat -> Nat
fib zero = zero
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n

fib-tail : Nat -> Nat -> Nat -> Nat
fib-tail zero a b = a
fib-tail (suc n) a b = fib-tail n b (a + b)

-- Division by 2
_/2 : Nat -> Nat
zero /2 = zero
(suc zero) /2 = zero
(suc (suc n)) /2 = suc (n /2)

div2 = _/2
