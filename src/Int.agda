open import Type using (Type)
open import Function using (_∘_)
open import Nat using (Nat; zero)
open import Coproduct using (_⨄_; inr; inl)
open import Identity using (_≡_; refl)

module Int where

-- Int : Type
-- Int = Nat ⨄ (Unit ⨄ Nat)
data Int : Type where
  in-neg : Nat -> Int
  zero : Int
  in-pos : Nat -> Int

neg-one : Int 
neg-one = in-neg 0

one : Int
one = in-pos 0

-- Induction principle
ind-int : {P : Int -> Type}
  -> P neg-one
  -> (∀ n -> P (in-neg n) -> P (in-neg (Nat.suc n)))
  -> P zero
  -> P one
  -> (∀ n -> P (in-pos n) -> P (in-pos (Nat.suc n)))
  -> (n : Int) -> P n
ind-int {P} pneg1 pnegS p0 p1 pposS = go
  where
    go : (n : Int) -> P n
    go (in-neg zero) = pneg1
    go (in-neg (Nat.suc n)) = pnegS n (go (in-neg n))
    go zero = p0
    go (in-pos zero) = p1
    go (in-pos (Nat.suc n)) = pposS n (go (in-pos n)) 

-- successor function
suc : Int -> Int
suc = ind-int pneg1 pnegS p0 p1 pposS
  where
    pneg1 : Int
    pneg1 = zero
    pnegS : Nat -> Int -> Int
    pnegS n _ = in-neg n
    p0 : Int
    p0 = one
    p1 : Int
    p1 = in-pos 1
    pposS : Nat -> Int -> Int
    pposS n _ = in-pos (Nat.suc (Nat.suc n)) 

{-
  Exercise 4.1.a
  Predecessor
-}
pred : Int -> Int
pred = ind-int pneg1 pnegS p0 p1 pposS
  where
    pneg1 : Int
    pneg1 = in-neg 1
    pnegS : Nat -> Int -> Int
    pnegS n _ = in-neg (Nat.suc (Nat.suc n))
    p0 : Int
    p0 = neg-one
    p1 : Int
    p1 = zero
    pposS : Nat -> Int -> Int
    pposS n _ = in-pos n

{-
  Exercise 4.1.b
  Group operations: add and neg
-}
_+_ : Int -> Int -> Int
x + in-neg zero = pred x
x + in-neg (Nat.suc y) = pred (x + (in-neg y))
x + zero = x
x + in-pos zero = suc x
x + in-pos (Nat.suc y) = suc (x + (in-pos y))

infixl 6  _+_

_ : zero + (in-neg 10) ≡ (in-neg 10)
_ = refl

_ : (in-neg 10) + zero ≡ (in-neg 10)
_ = refl

_ : (in-pos 12) + (in-neg 5) ≡ (in-pos 6)
_ = refl

_ : (in-neg 1) + (in-neg 2) ≡ (in-neg 4)
_ = refl

_ : (in-neg 3) + (in-pos 5) ≡ (in-pos 1)
_ = refl

_ : (in-pos 3) + (in-neg 5) ≡ (in-neg 1)
_ = refl

-_ : Int -> Int
- in-neg x = in-pos x
- zero = zero
- in-pos x = in-neg x

_-_ : Int -> Int -> Int
x - y = x + (- y)

infixl 6  _-_

{-
  Exercise 4.1.c
  multiplication    
-}
_*_ : Int -> Int -> Int
x * in-neg zero = - x
x * in-neg (Nat.suc y) = - (x + (x * in-pos y))
x * zero = zero
x * in-pos zero = x
x * in-pos (Nat.suc y) = x + (x * (in-pos y))

_ : zero * (in-neg 10) ≡ zero
_ = refl

_ :  (in-neg 10) * zero ≡ zero
_ = refl

_ : (in-pos 2) * (in-pos 3) ≡ (in-pos 11)
_ = refl 

_ : (in-neg 2) * (in-pos 3) ≡ (in-neg 11)
_ = refl

_ : (in-pos 2) * (in-neg 3) ≡ (in-neg 11)
_ = refl

_ : (in-neg 2) * (in-neg 3) ≡ (in-pos 11)
_ = refl

infixl 7  _*_
