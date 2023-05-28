import Nat
open import Int
open import Int.Properties.Suc using (suc-pred; pred-suc)
import Int.Properties.Add as Add
import Int.Properties.Neg as Neg
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Minus where

left-neg : ∀ x y -> (- x) + y ≡ y - x
left-neg x y = Add.commutative (- x) y

itself : ∀ x -> x - x ≡ zero
itself = Add.right-inv

add-zero-left : ∀ x y -> (x - x) + y ≡ y 
add-zero-left x y rewrite itself x = Add.left-unit y

add-zero-right : ∀ x y -> x + (y - y) ≡ x
add-zero-right x y rewrite itself y = refl

add-zero-ends : ∀ x y -> x + y - x ≡ y
add-zero-ends x y 
  rewrite Add.swap-right x y (- x)
  | inv (Add.assoc x (- x) y) = add-zero-left x y
