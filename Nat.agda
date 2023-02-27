open import Equality using (_≡_; refl; cong; cong-app)
open Equality.≡-Reasoning

module Nat where

  Type = Set

  data Nat : Type where
    zero : Nat
    suc : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

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
  module _ where 
    add-zero-right : Nat -> Nat
    add-zero-right m = m

    add-suc-right : Nat -> Nat -> Nat -> Nat 
    add-suc-right m n = suc

    add-right-ind : Nat -> Nat -> Nat
    add-right-ind m = ind-nat (add-zero-right m) (add-suc-right m)

    _ : add-right-ind 2 5 ≡ 7
    _ = refl

    {-
      This proof can also be expressed in terms of the induction principle ind-nat,
      where P n = add-right-ind m n ≡ m + n 
    -}
    add-eq : ∀ m n -> add-right-ind m n ≡ m + n
    add-eq m zero = refl
    add-eq m (suc n) = 
      begin
        add-right-ind m (suc n)
      ≡⟨⟩
        ind-nat (add-zero-right m) (add-suc-right m) (suc n)
      ≡⟨⟩
        add-suc-right m n (ind-nat (add-zero-right m) (add-suc-right m) n)
      ≡⟨⟩
        add-suc-right m n (add-right-ind m n)
      ≡⟨⟩
        suc (add-right-ind m n)
      ≡⟨ cong suc (add-eq m n) ⟩
        suc (m + n)
      ∎

    add-eq-ind : ∀ m n -> add-right-ind m n ≡ m + n
    add-eq-ind m = ind-nat p0 ps
      where
        P : Nat -> Type
        P x = add-right-ind m x ≡ m + x

        p0 : P zero
        p0 = refl

        ps : (n : Nat) -> P n -> P (suc n)
        ps n IH = 
          begin
            add-right-ind m (suc n)
          ≡⟨⟩
            ind-nat (add-zero-right m) (add-suc-right m) (suc n)
          ≡⟨⟩
            add-suc-right m n (ind-nat (add-zero-right m) (add-suc-right m) n)
          ≡⟨⟩
            add-suc-right m n (add-right-ind m n)
          ≡⟨⟩
            suc (add-right-ind m n)
          ≡⟨ cong suc IH ⟩
            suc (m + n)
          ∎

  {-
    Exercise 3.1.a
    Multiplication
  -}
  _*_ : Nat -> Nat -> Nat
  m * zero = zero
  m * suc n = m + (m * n)

  -- In terms of the induction principle
  module _ where
    mul-zero-right : Nat -> Nat
    mul-zero-right m = zero

    mul-suc-right : Nat -> Nat -> Nat -> Nat
    mul-suc-right m n next = m + next

    {-
        mul-right-ind m zero
      = ind-nat p0 ps zero
      = p0
      = mul-zero-right m
      = zero

        mul-right-ind m (suc n)
      = ind-nat p0 ps (suc n)
      = ps n (ind-nat p0 ps n)
      = mul-suc-right m n (ind-nat p0 ps n)
      = m + (ind-nat p0 ps n)
      = m + (mul-right-ind m n)
    -}
    mul-right-ind : Nat -> Nat -> Nat
    mul-right-ind m = ind-nat (mul-zero-right m) (mul-suc-right m)

    _ : mul-right-ind 2 5 ≡ 10
    _ = refl

    mul-eq : ∀ m n -> mul-right-ind m n ≡ m * n
    mul-eq m zero = refl
    mul-eq m (suc n) = 
      begin
        mul-right-ind m (suc n)
      ≡⟨⟩
        ind-nat (mul-zero-right m) (mul-suc-right m) (suc n)
      ≡⟨⟩
        mul-suc-right m n (ind-nat (mul-zero-right m) (mul-suc-right m) n)
      ≡⟨⟩
        mul-suc-right m n (mul-right-ind m n)
      ≡⟨⟩
        m + mul-right-ind m n
      ≡⟨ cong (m +_) (mul-eq m n) ⟩
        m + (m * n)
      ∎

  {-
    Exercise 3.1.a
    Exponentiation
  -}
  _^_ : Nat -> Nat -> Nat
  m ^ zero = 1
  m ^ suc n = m * (m ^ n)

  -- In terms of the induction principle
  module _ where
    exp-zero : Nat -> Nat
    exp-zero m = 1

    exp-suc : Nat -> Nat -> Nat -> Nat
    exp-suc m n next = m * next

    {-
        exp m zero
      = ind-nat p0 ps zero
      = p0
      = exp-zero m
      = 1

        exp m (suc n)
      = ind-nat p0 ps (suc n)
      = ps n (ind-nat p0 ps n)
      = exp-suc m n (ind-nat p0 ps n)
      = m * (ind-nat p0 ps n)
      = m * (exp m n)
    -}
    exp : Nat -> Nat -> Nat
    exp m = ind-nat (exp-zero m) (exp-suc m)

    _ : exp 2 5 ≡ 32
    _ = refl

    exp-eq : ∀ m n -> exp m n ≡ m ^ n
    exp-eq m zero = refl
    exp-eq m (suc n) = 
      begin
        exp m (suc n)
      ≡⟨⟩
        ind-nat (exp-zero m) (exp-suc m) (suc n)
      ≡⟨⟩
        exp-suc m n (ind-nat (exp-zero m) (exp-suc m) n)
      ≡⟨⟩
        exp-suc m n (exp m n)
      ≡⟨⟩
        m * exp m n
      ≡⟨ cong (m *_) (exp-eq m n) ⟩
        m * (m ^ n)
      ∎

  {-
    Exercise 3.2
    min and max
  -}
  min : Nat -> Nat -> Nat
  min m zero = zero
  min zero n = zero
  min (suc m) (suc n) = suc (min m n)

  max : Nat -> Nat -> Nat
  max m zero = m
  max zero n = n
  max (suc m) (suc n) = suc (max m n)

  -- In terms of the induction principle
  module _ where
    min-zero : Nat -> Nat
    min-zero _ = zero

    min-suc : Nat -> (Nat -> Nat) -> Nat -> Nat
    min-suc m next n = ind-nat zero (λ n' -> λ _ -> suc (next n')) n

    min-ind : Nat -> Nat -> Nat
    min-ind = ind-nat min-zero min-suc

    _ : min-ind 0 10 ≡ 0
    _ = refl

    _ : min-ind 10 0 ≡ 0
    _ = refl

    _ : min-ind 10 12 ≡ 10
    _ = refl
 
    _ : min-ind 25 20 ≡ 20
    _ = refl

    min-eq : ∀ m n -> min-ind m n ≡ min m n
    min-eq zero zero = refl
    min-eq (suc m) zero = refl
    min-eq zero (suc n) = refl
    min-eq (suc m) (suc n) = 
      begin
        min-ind (suc m) (suc n)
      ≡⟨⟩
        ind-nat min-zero min-suc (suc m) (suc n)
      ≡⟨⟩
        min-suc m (ind-nat min-zero min-suc m) (suc n)
      ≡⟨⟩
        min-suc m (min-ind m) (suc n)
      ≡⟨⟩
        ind-nat zero (λ n' -> λ (_ : Nat) -> suc (min-ind m n')) (suc n)
      ≡⟨⟩
        (λ n' -> λ _ -> suc (min-ind m n')) n (min-suc m (min-ind m) n)
      ≡⟨⟩
        (λ _ -> suc (min-ind m n)) (min-suc m (min-ind m) n)
      ≡⟨⟩
        suc (min-ind m n)
      ≡⟨ cong suc (min-eq m n) ⟩
        suc (min m n)
      ∎
