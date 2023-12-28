import Nat
open import Int.Base
open import Int.Suc
open import Int.Neg
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

-- TODO: use better module organization
module Int.Add where

{-
  Exercise 5.7.a
-}
right-unit : ∀ x -> x + zero ≡ x
right-unit x = refl

left-unit : ∀ x -> zero + x ≡ x
left-unit (in-neg Nat.zero) = refl
left-unit (in-neg (Nat.suc n)) =
  begin
    pred (zero + in-neg n)
  ≡⟨ ap pred (left-unit (in-neg n)) ⟩
    pred (in-neg n)
  ≡⟨ pred-neg n ⟩
    in-neg (Nat.suc n)
  ∎
left-unit zero = refl
left-unit (in-pos Nat.zero) = refl
left-unit (in-pos (Nat.suc n)) =
  begin
    suc (zero + in-pos n)
  ≡⟨ ap suc (left-unit (in-pos n)) ⟩
    suc (in-pos n)
  ≡⟨ suc-pos n ⟩
    in-pos (Nat.suc n)
  ∎

{-
  Exercise 5.7.b
-}
pred-right : ∀ x y -> x + pred y ≡ pred (x + y)
{-
    x + pred (in-neg zero)
  = x + in-neg (suc zero)
  = pred (x + in-neg (suc zero))
  = pred (pred x)
-}
pred-right x (in-neg Nat.zero) = refl
{-
    x + pred (in-neg (suc y))
  = x + in-neg (suc (suc y))
  = pred (x + in-neg (suc y))
  = pred (pred (x + in-neg y))
-}
pred-right x (in-neg (Nat.suc y)) = refl
-- x + pred zero = pred (x + zero) = pred x
pred-right x zero = refl
{-
  x + pred (in-pos zero) = x + zero = x
  pred (x + in-pos zero) = pred (suc x) = x
-}
pred-right x (in-pos Nat.zero) rewrite pred-suc x = refl
pred-right x (in-pos (Nat.suc y)) =
  begin
    x + pred (in-pos (Nat.suc y))
  ≡⟨ ap (x +_) (pred-pos y) ⟩
    x + in-pos y
  ≡⟨ inv (pred-suc (x + in-pos y)) ⟩
    pred (suc (x + in-pos y))
  ∎

pred-left : ∀ x y -> pred x + y ≡ pred (x + y)
-- pred x + in-neg zero = pred (pred x)
pred-left x (in-neg Nat.zero) = refl
pred-left x (in-neg (Nat.suc y)) =
  begin
    pred x + in-neg (Nat.suc y)
  ≡⟨⟩
    pred (pred x + in-neg y)
  ≡⟨ ap pred (pred-left x (in-neg y)) ⟩
    pred (pred (x + in-neg y))
  ≡⟨⟩
    pred (x + in-neg (Nat.suc y))
  ∎
pred-left x zero = refl
pred-left x (in-pos Nat.zero) rewrite suc-pred-eq x = refl
pred-left x (in-pos (Nat.suc y)) =
  begin
    pred x + in-pos (Nat.suc y)
  ≡⟨⟩
    suc (pred x + in-pos y)
  ≡⟨ ap suc (pred-left x (in-pos y)) ⟩
    suc (pred (x + in-pos y))
  ≡⟨ suc-pred-eq (x + in-pos y) ⟩
    pred (suc (x + in-pos y))
  ≡⟨⟩
    pred (x + in-pos (Nat.suc y))
  ∎

right-suc : ∀ x y -> x + suc y ≡ suc (x + y)
{-
  x + (suc (in-neg zero)) = x + zero = x
  suc (x + (in-neg zero)) = suc (pred x) = x
-}
right-suc x (in-neg Nat.zero) rewrite suc-pred x = refl
{-
    x + suc (in-neg (suc y))
  = x + in-neg y

    suc (x + in-neg (suc y))
  = suc (pred (x + in-neg y))
  = x + in-neg y
-}
right-suc x (in-neg (Nat.suc y))
  rewrite suc-pred (x + in-neg y) = refl
right-suc x zero = refl
-- x + suc (in-pos zero) = x + in-pos (suc zero) = suc (x + in-pos zero)
right-suc x (in-pos Nat.zero) = refl
{-
    x + suc (in-pos (suc y))
  = x + in-pos (suc (suc y))
  = suc (x + in-pos (suc y))
  = suc (suc (x + in-pos y))

    suc (x + in-pos (suc y))
  = suc (suc (x + in-pos y))
-}
right-suc x (in-pos (Nat.suc y)) = refl

left-suc : ∀ x y -> suc x + y ≡ suc (x + y)
{-
  suc x + in-neg zero = pred (suc x) = x
  suc (x + in-neg zero) = suc (pred x) = x
-}
left-suc x (in-neg Nat.zero) rewrite suc-pred-eq x = refl
{-
    suc x + in-neg (suc y)
  = pred (suc x + in-neg y)
  = pred (suc (x + in-neg y)) [I.H]

    suc (x + in-neg (suc y))
  = suc (pred (x + in-neg y))
-}
left-suc x (in-neg (Nat.suc y))
  rewrite left-suc x (in-neg y)
  | suc-pred-eq (x + in-neg y) = refl
left-suc x zero = refl
{-
  suc x + in-pos zero = suc (suc x)
  suc (x + in-pos zero) = suc (suc x)
-}
left-suc x (in-pos Nat.zero) = refl
{-
    suc x + in-pos (suc y)
  = suc (suc x + in-pos y)
  = suc (suc (x + in-pos y)) [I.H]

    suc (x + in-pos (suc y))
  = suc (suc (x + in-pos y))
-}
left-suc x (in-pos (Nat.suc y)) rewrite left-suc x (in-pos y) = refl

{-
  Exercise 5.7.c
  Associativity and Commutativity
-}
assoc : ∀ x y z -> (x + y) + z ≡ x + (y + z)
{-
  (x + y) + in-neg zero = pred (x + y)
  x + (y + in-neg zero) = x + pred y
-}
assoc x y (in-neg Nat.zero) rewrite pred-right x y = refl
{-
    (x + y) + in-neg (suc z)
  = pred((x + y) + in-neg z)
  = pred(x + (y + in-neg z)) [I.H]
  = x + (pred (y + in-neg z)) [pred-right]

    x + (y + in-neg (suc z))
  = x + (pred (y + in-neg z))
-}
assoc x y (in-neg (Nat.suc z))
  rewrite assoc x y (in-neg z)
  | pred-right x (y + in-neg z) = refl
assoc x y zero = refl
{-
  (x + y) + in-pos zero = suc (x + y)
  x + (y + in-pos zero) = x + (suc y)
-}
assoc x y (in-pos Nat.zero) rewrite right-suc x y = refl
{-
    (x + y) + in-pos (suc z)
  = suc ((x + y) + in-pos z)
  = suc (x + (y + in-pos z)) [I.H]
  = x + suc (y + in-pos z) [right-suc]

    x + (y + in-pos (suc z))
  = x + suc (y + in-pos z)
-}
assoc x y (in-pos (Nat.suc z))
  rewrite assoc x y (in-pos z)
  | right-suc x (y + in-pos z) = refl

commutative : ∀ x y -> x + y ≡ y + x
{-
  x + in-neg zero = pred x
  in-neg zero + x = pred zero + x = pred (zero + x) = pred x
-}
commutative x (in-neg Nat.zero)
  rewrite pred-zero
  | pred-left zero x
  | left-unit x = refl
{-
    x + (in-neg (suc y))
  = pred (x + in-neg y)

    in-neg (suc y) + x
  = pred (in-neg y) + x [pred-neg]
  = pred (in-neg y + x) [pred-left]
  = pred (x + in-neg y) [I.H]
-}
commutative x (in-neg (Nat.suc y))
  rewrite commutative x (in-neg y)
  | inv (pred-neg y)
  | pred-left (in-neg y) x = refl
commutative x zero rewrite left-unit x = refl
{-
  x + (in-pos zero) = suc x
  (in-pos zero) + x = suc zero + x = suc (zero + x) = suc x
-}
commutative x (in-pos Nat.zero)
  rewrite suc-zero
  | left-suc zero x
  | left-unit x = refl
{-
    x + (in-pos (suc y))
  = suc (x + in-pos y)

    in-pos (suc y) + x
  = suc (in-pos y) + x
  = suc (in-pos y + x)
  = suc (x + in-pos y) [I.H]
-}
commutative x (in-pos (Nat.suc y))
  rewrite commutative x (in-pos y)
  | inv (suc-pos y)
  | left-suc (in-pos y) x = refl

{-
  Exercise 5.7.d
  Left and right inverses
-}
left-inv : ∀ x -> (- x) + x ≡ zero
-- (- in-neg zero) + (in-neg zero) = in-pos zero + in-neg zero = pred (in-pos zero) = zero
left-inv (in-neg Nat.zero) = refl
-- TODO: Check why rewriting generates an error with the termination checker
left-inv (in-neg (Nat.suc x)) =
  begin
    pred (in-pos (Nat.suc x) + in-neg x)
  ≡⟨ ap pred (commutative (in-pos (Nat.suc x)) (in-neg x)) ⟩
    pred (in-neg x + in-pos (Nat.suc x))
  ≡⟨⟩
    pred (suc (in-neg x + in-pos x))
  ≡⟨ pred-suc (in-neg x + in-pos x) ⟩
    in-neg x + in-pos x
  ≡⟨ ap (_+ in-pos x) (inv (pos-inv x)) ⟩
    (- in-pos x) + in-pos x
  ≡⟨ left-inv (in-pos x) ⟩
    zero
  ∎
left-inv zero = refl
left-inv (in-pos Nat.zero) = refl
left-inv (in-pos (Nat.suc x)) = begin
    suc (in-neg (Nat.suc x) + in-pos x)
  ≡⟨ ap suc (commutative (in-neg (Nat.suc x)) (in-pos x)) ⟩
    suc (in-pos x + in-neg (Nat.suc x))
  ≡⟨⟩
    suc (pred (in-pos x + in-neg x))
  ≡⟨ suc-pred (in-pos x + in-neg x) ⟩
    in-pos x + in-neg x
  ≡⟨ ap (_+ in-neg x) (inv (neg-inv x)) ⟩
    (- in-neg x) + in-neg x
  ≡⟨ left-inv (in-neg x) ⟩
    zero
  ∎

right-inv : ∀ x -> x + (- x) ≡ zero
right-inv x rewrite commutative x (- x) = left-inv x

swap-right : ∀ x y z -> x + y + z ≡ x + (z + y)
swap-right x y z rewrite assoc x y z | commutative y z = refl

swap-left : ∀ x y z -> x + y + z ≡ y + (x + z)
swap-left x y z rewrite commutative x y | assoc y x z = refl

add-pos : ∀ m n -> in-pos m + in-pos n ≡ pred (in-pos (Nat._+_ (Nat.suc m) (Nat.suc n)))
add-pos m Nat.zero rewrite pred-pos (Nat.suc m) = suc-pos m
add-pos m (Nat.suc n)
  rewrite add-pos m n
  | suc-pred (in-pos (Nat.add (Nat.suc m) (Nat.suc n))) = refl

add-neg : ∀ m n -> in-neg m + in-neg n ≡ suc (in-neg (Nat._+_ (Nat.suc m) (Nat.suc n)))
add-neg m Nat.zero rewrite suc-neg (Nat.suc m) = pred-neg m
add-neg m (Nat.suc n)
  rewrite add-neg m n
  | pred-suc (in-neg (Nat._+_ (Nat.suc m) (Nat.suc n))) = refl
