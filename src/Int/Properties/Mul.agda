import Nat
open import Int
open import Int.Properties.Suc
import Int.Properties.Neg as Neg
import Int.Properties.Add as Add
import Int.Properties.Minus as Minus
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
  | Neg.pos-inv x = refl
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
right-pred x (in-neg Nat.zero) = Neg.distrib-+ x x
{-
    x * pred (in-neg (suc y))
  = x * in-neg (suc (suc y))
  = - (x + x * in-pos (suc y))
  = - (x + (x + x * in-pos y))
  = (- x) + (x + x * in-pos y)

    x * (in-neg (suc y)) - x
  = (- (x + x * in-pos y)) - x
-}
right-pred x (in-neg (Nat.suc y))
  rewrite Neg.distrib-+ x (x + x * in-pos y)
  | Minus.left-neg x (- (x + x * in-pos y)) = refl
right-pred x zero = inv (Add.left-unit (- x))
{-
  x * pred (in-pos zero) = x * zero = zero
  x * (in-pos zero) - x = x - x
-}
right-pred x (in-pos Nat.zero) = inv (Minus.itself x)
{-
  x * pred (in-pos (Nat.suc y)) = x * in-pos y
  (x + x * in-pos (suc y)) - x
-}
right-pred x (in-pos (Nat.suc y))
  rewrite pred-pos y
  | Add.assoc x (x * in-pos y) (- x)
  | Add.commutative (x * in-pos y) (- x)
  | inv (Add.assoc x (- x) (x * in-pos y)) 
  | Minus.itself x
  | Add.left-unit (x * in-pos y) = refl

left-pred : ∀ x y -> pred x * y ≡ x * y - y
left-pred x (in-neg Nat.zero) 
  rewrite Neg.distrib-+ x (in-neg Nat.zero) = refl
{-
    pred x * in-neg (suc y)
  = - (pred x + (pred x * in-pos y))
  = - (pred x + (x * in-pos y - in-pos y)) [I.H]
  = (- pred x) + (- (x * in-pos y - in-pos y))
  = suc (- x) + (in-pos y - x * in-pos y)
  = suc (- x + in-pos y - x * in-pos y)

    x * in-neg (suc y) - in-neg (suc y)
  = x * in-neg (suc y) + in-pos (suc y)
  = suc (x * in-neg (suc y) + in-pos y)
  = suc (- (x + x * in-pos y) + in-pos y) 
-}
left-pred x (in-neg (Nat.suc y))
  rewrite left-pred x (in-pos y)
  | Neg.distrib-+ (pred x) (x * in-pos y - in-pos y) 
  | Neg.pred-inv x 
  | Add.suc-left (- x) (- (x * in-pos y - in-pos y))
  | Neg.distrib-+ (x * in-pos y) (in-neg y)
  | inv (Add.assoc (- x) (- (x * in-pos y)) (in-pos y))
  | Neg.distrib-+ x (x * in-pos y)  = refl
left-pred x zero = refl
left-pred x (in-pos Nat.zero) = refl
left-pred x (in-pos (Nat.suc y))
  rewrite left-pred x (in-pos y)
  | Add.pred-left x (x * in-pos y + in-neg y)
  | Add.assoc x (x * in-pos y) (in-neg y) = refl
 