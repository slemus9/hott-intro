open import Equality using (_≡_; refl; cong; cong-app)
open Equality.≡-Reasoning

module Nat where

  Type = Set

  data Nat : Type where
    zero : Nat
    suc : Nat -> Nat

  
  {-
    Induction principle:
    Ctx, x : Nat |- P x
             Ctx |- p0 : P zero
             Ctx |- ps : (n : Nat) -> P n -> P (suc n)
    --------------------------------------------------
    Ctx, x : Nat |- ind(p0, ps, x) : (n : Nat) -> P x

    Computation rules: 
    Ctx, x : Nat |- P x
             Ctx |- p0 : P zero
             Ctx |- ps : (n : Nat) -> P n -> P (suc n)
    --------------------------------------------------
    Ctx |- ind(p0, ps, zero) = p0 : P zero

    Ctx, x : Nat |- P x
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
  zero + m = m
  suc n + m = suc (n + m)

  {-
    Addition with the induction principle on the second argument
    m : Nat |- add(m) : Nat -> Nat
  -}