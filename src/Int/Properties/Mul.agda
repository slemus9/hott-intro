import Nat
open import Int
open import Int.Properties.Suc
open import Int.Properties.Neg
import Int.Properties.Add as Add
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Mul where

{-
  Exercise 5.8.a
-}
right-unit : ∀ x -> x * one ≡ x
right-unit x = refl

left-unit : ∀ x -> one * x ≡ x
left-unit (in-neg Nat.zero) = refl
{-
    one * in-neg (suc x)
  = - (one + (one * in-pos x))
  = - (one + in-pos x) [I.H]
  = - (in-pos zero + in-pos x)
  = - (in-pos x + in-pos zero)
  = - (suc (in-pos x))
  = - in-pos (suc x)
  = in-neg (suc x)
-}
left-unit (in-neg (Nat.suc x))
  rewrite left-unit (in-pos x)
  | Add.commutative (in-pos 0) (in-pos x)
  | suc-pos x
  | pos-inv x = refl
left-unit zero = refl
left-unit (in-pos Nat.zero) = refl
left-unit (in-pos (Nat.suc x))
  rewrite left-unit (in-pos x)
  | Add.commutative (in-pos 0) (in-pos x)
  | suc-pos x = refl

right-zero : ∀ x -> x * zero ≡ zero
right-zero x = refl

left-zero : ∀ x -> zero * x ≡ zero
left-zero (in-neg Nat.zero) = refl
left-zero (in-neg (Nat.suc x)) rewrite left-zero (in-pos x) = refl
left-zero zero = refl
left-zero (in-pos Nat.zero) = refl
left-zero (in-pos (Nat.suc x)) rewrite left-zero (in-pos x) = refl

{-
  Exercise 5.8.b

  predecessor and successor laws
-}
right-pred : ∀ x y -> x * pred y ≡ x * y - x
{-
    x * pred (in-neg zero) 
  = x * (in-neg (suc zero))
  = - (x + x * in-pos zero)
  = - (x + x)
  
  x * in-neg zero - x = (- x) - x = (- x) + (- x)
-}
right-pred x (in-neg Nat.zero) = {!   !}
right-pred x (in-neg (Nat.suc y)) = {!   !}
right-pred x zero = {!   !}
right-pred x (in-pos y) = {!   !}
