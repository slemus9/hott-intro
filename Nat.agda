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
  m + zero = m
  m + suc n = suc (m + n)

  {-
    Addition with the induction principle on the second argument
    m : Nat |- add(m) : Nat -> Nat. We have the constant family 
    P(n) := Nat

    Ctx, x : Nat |- Nat
             Ctx |- p0 : Nat
             Ctx |- ps : (n : Nat) -> Nat -> Nat
    --------------------------------------------------
    Ctx, x : Nat |- ind(p0, ps, x) : (n : Nat) -> Nat

    Definitions:
    add-zero m = m
    add-succ-right m n x = suc x
    add-right-ind m = ind-nat (add-zero-right m) (add-succ-right m)

    Let:
    p0 := add-zero m 
    ps := add-suc m 

    Computation:
      add-right-ind m zero
    = ind-nat p0 ps zero
    = p0
    = add-zero m
    = m

      add-right-ind m (suc n)
    = ind-nat p0 ps (suc n)
    = ps n (ind-nat p0 ps n)
    = add-suc m n (ind-nat p0 ps n)
    = suc (ind-nat p0 ps n)
    = suc (add-right-ind m n)
  -}
  add-zero-right : Nat -> Nat
  add-zero-right m = m

  add-succ-right : Nat -> Nat -> Nat -> Nat 
  add-succ-right m n = suc

  add-right-ind : Nat -> Nat -> Nat
  add-right-ind m = ind-nat (add-zero-right m) (add-succ-right m)