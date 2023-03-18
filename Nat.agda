open import Function using (id)
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
    -- min
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
  
    -- max 
    max-suc : Nat -> (Nat -> Nat) -> Nat -> Nat
    max-suc m next = ind-nat (suc m) (λ n -> λ _ -> suc (next n))

    max-ind : Nat -> Nat -> Nat
    max-ind = ind-nat id max-suc 

    _ : max-ind 10 0 ≡ 10
    _ = refl

    _ : max-ind 0 10 ≡ 10
    _ = refl

    _ : max-ind 23 25 ≡ 25
    _ = refl

    _ : max-ind 11 8 ≡ 11
    _ = refl

    max-eq : ∀ m n -> max-ind m n  ≡ max m n
    max-eq zero zero = refl
    max-eq zero (suc n) = refl
    max-eq (suc m) zero = refl
    max-eq (suc m) (suc n) = 
      begin
        max-ind (suc m) (suc n)
      ≡⟨⟩
        ind-nat id max-suc (suc m) (suc n)
      ≡⟨⟩
        max-suc m (max-ind m) (suc n)
      ≡⟨⟩
        ind-nat (suc m) (λ n -> λ (_ : Nat) -> suc (max-ind m n)) (suc n)
      ≡⟨⟩
        (λ n -> λ _ -> suc (max-ind m n)) n (max-suc m (max-ind m) n)
      ≡⟨⟩
        (λ _ -> suc (max-ind m n)) (max-suc m (max-ind m) n)
      ≡⟨⟩
        suc (max-ind m n)
      ≡⟨ cong suc (max-eq m n) ⟩
        suc (max m n)
      ∎ 

  {-
    Exercise 3.3.a
    triangular numbers
  -}
  triangular : Nat -> Nat
  triangular zero = zero
  triangular (suc n) = (suc n) + triangular n

  _ : triangular 10 ≡ 55
  _ = refl

  -- In terms of the induction principle
  -- TODO: Make it tail recursive and prove that both definitions are equivalent
  module _ where
    triangular-ind : Nat -> Nat
    triangular-ind = ind-nat zero (λ n -> λ next -> (suc n) + next)

    _ : triangular-ind 10 ≡ 55
    _ = refl

    triangular-eq : ∀ n -> triangular-ind n ≡ triangular n
    triangular-eq zero = refl
    triangular-eq (suc n) = 
      begin
        triangular-ind (suc n)
      ≡⟨⟩
        ind-nat zero (λ n -> λ next -> (suc n) + next) (suc n)
      ≡⟨⟩
        (λ n -> λ next -> (suc n) + next) n (ind-nat zero (λ n -> λ next -> (suc n) + next) n)
      ≡⟨⟩
        (λ n -> λ next -> (suc n) + next) n (triangular-ind n)
      ≡⟨⟩
        (λ next -> (suc n) + next) (triangular-ind n)
      ≡⟨⟩
        (suc n) + triangular-ind n
      ≡⟨ cong ((suc n) +_) (triangular-eq n) ⟩
        (suc n) + triangular n
      ∎

  {-
    Exercise 3.3.b
    factorial
  -}
  _! : Nat -> Nat
  zero ! = 1
  (suc n) ! = suc n * (n !)

  fact : Nat -> Nat
  fact = _!

  _ : 5 ! ≡ 120
  _ = refl

  -- In terms of the induction principle
  -- TODO: Make it tail recursive and prove that both definitions are equivalent
  module _ where
    fact-ind : Nat -> Nat
    fact-ind = ind-nat 1 (λ n -> λ next -> (suc n) * next)

    fact-eq : ∀ n -> fact-ind n ≡ n !
    fact-eq zero = refl
    fact-eq (suc n) = 
      begin
        fact-ind (suc n)
      ≡⟨⟩
        ind-nat 1 (λ n -> λ next -> (suc n) * next) (suc n)
      ≡⟨⟩
        (λ n -> λ next -> (suc n) * next) n (fact-ind n)
      ≡⟨⟩
        (λ next -> (suc n) * next) (fact-ind n)
      ≡⟨⟩
        (suc n) * (fact-ind n)
      ≡⟨ cong ((suc n) *_) (fact-eq n)⟩
        suc n * (n !)
      ∎

  {-
    Exercise 3.4
    Binomial coefficient
  -}
  bin-coef : Nat -> Nat -> Nat
  bin-coef zero zero = 1
  bin-coef zero (suc k) = zero
  bin-coef (suc n) zero = 1
  bin-coef (suc n) (suc k) = (bin-coef n k) + (bin-coef n (suc k))

  _ : bin-coef 5 11 ≡ 0
  _ = refl

  _ : bin-coef 11 5 ≡ 462
  _ = refl

  _ : bin-coef 11 11 ≡ 1
  _ = refl

  -- In terms of the induction principle
  module _ where
    bin-coef-zero : Nat -> Nat 
    bin-coef-zero = ind-nat 1 (λ _ -> λ _ -> zero)

    bin-coef-suc : Nat -> (Nat -> Nat) -> Nat -> Nat
    bin-coef-suc _ next = ind-nat 1 (λ k -> λ _ -> next k + next (suc k))

    bin-coef-ind : Nat -> Nat -> Nat
    bin-coef-ind = ind-nat bin-coef-zero bin-coef-suc

    _ : bin-coef-ind 11 5 ≡ 462
    _ = refl

    bin-coef-eq : ∀ n k -> bin-coef-ind n k  ≡ bin-coef n k
    bin-coef-eq zero zero = refl
    bin-coef-eq zero (suc k) = refl
    bin-coef-eq (suc n) zero = refl
    bin-coef-eq (suc n) (suc k) = 
      begin
        bin-coef-ind (suc n) (suc k)
      ≡⟨⟩
        ind-nat bin-coef-zero bin-coef-suc (suc n) (suc k)
      ≡⟨⟩
        bin-coef-suc n (ind-nat bin-coef-zero bin-coef-suc n) (suc k)
      ≡⟨⟩
        bin-coef-suc n (bin-coef-ind n) (suc k)
      ≡⟨⟩
        ind-nat 1 (λ k -> λ (_ : Nat) -> bin-coef-ind n k + bin-coef-ind n (suc k)) (suc k)
      ≡⟨⟩
        (λ k -> λ _ -> bin-coef-ind n k + bin-coef-ind n (suc k)) k (bin-coef-suc n (bin-coef-ind n) k)
      ≡⟨⟩
        (λ _ -> bin-coef-ind n k + bin-coef-ind n (suc k)) (bin-coef-suc n (bin-coef-ind n) k)
      ≡⟨⟩
        bin-coef-ind n k + bin-coef-ind n (suc k)
      ≡⟨ cong (_+ bin-coef-ind n (suc k)) (bin-coef-eq n k) ⟩
        bin-coef n k + bin-coef-ind n (suc k)
      ≡⟨ cong (bin-coef n k +_) (bin-coef-eq n (suc k)) ⟩
        bin-coef n k + bin-coef n (suc k)
      ∎

  {-
    Exercise 3.5
    Fibonacci

    a b
    0 0 -> 0
    0 1 -> 1
    1 1 -> 2
    1 2 -> 3
    2 3 -> 5
    3 5 -> 8
    5 8 -> 13
  -}
  fib : Nat -> Nat
  fib zero = zero
  fib 1 = 1
  fib (suc (suc n)) = fib (suc n) + fib n

  fib-tail : Nat -> Nat -> Nat -> Nat
  fib-tail zero a b = a
  fib-tail (suc n) a b = fib-tail n b (a + b)

  _ : fib-tail 9 0 1 ≡ 34
  _ = refl

  fib-zero : Nat -> Nat -> Nat
  fib-zero a _ = a

  fib-suc : Nat -> (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat
  fib-suc _ next a b = next b (a + b)

  fib-ind : Nat -> Nat
  fib-ind n = ind-nat fib-zero fib-suc n 0 1

  _ : fib-ind 9 ≡ 34
  _ = refl

  -- fib-tail-corresp : ∀ n m ->
  --   fib-tail (suc n) (fib m) (fib (suc m)) ≡ fib-tail n (fib (suc m)) (fib (suc (suc m)))
  -- fib-tail-corresp zero m = refl
  -- fib-tail-corresp (suc n) m = {!   !}

  -- fib-fib-tail-eq : ∀ n -> fib n ≡ fib-tail n 0 1
  -- fib-fib-tail-eq = {!   !}

  {-
    Exercise 3.4
    Division by two
  -}
  _/2 : Nat -> Nat
  zero /2 = zero
  (suc zero) /2 = zero
  (suc (suc n)) /2 = suc (n /2)

  div2 : Nat -> Nat
  div2 zero = zero
  div2 (suc n) = go n
    where
      go : Nat -> Nat
      go zero = zero
      go (suc n) = suc (div2 n) 

  div2-tail : Nat -> Nat -> Nat
  div2-tail acc zero = acc
  div2-tail acc (suc zero) = acc
  div2-tail acc (suc (suc n)) = div2-tail (suc acc) n

  _ : 2 /2 ≡ 1
  _ = refl

  _ : 10 /2 ≡ 5
  _ = refl

  _ : 11 /2 ≡ 5
  _ = refl

  _ : 12 /2 ≡ 6
  _ = refl
