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
itself (in-neg Nat.zero) = refl
itself (in-neg (Nat.suc x)) = 
  begin
    suc (in-neg (Nat.suc x) + in-pos x)
  ≡⟨ ap suc (Add.commutative (in-neg (Nat.suc x)) (in-pos x)) ⟩
    suc (in-pos x + in-neg (Nat.suc x))
  ≡⟨⟩
    suc (pred (in-pos x + in-neg x))
  ≡⟨ suc-pred (in-pos x + in-neg x) ⟩
    in-pos x + in-neg x
  ≡⟨ ap (in-pos x +_) (inv (Neg.pos-inv x)) ⟩
    in-pos x + (- in-pos x)
  ≡⟨ itself (in-pos x) ⟩
    zero
  ∎
itself zero = refl
itself (in-pos Nat.zero) = refl
itself (in-pos (Nat.suc x)) = 
  begin
    pred (in-pos (Nat.suc x) + in-neg x)
  ≡⟨ ap pred (Add.commutative (in-pos (Nat.suc x)) (in-neg x)) ⟩
    pred (in-neg x + in-pos (Nat.suc x))
  ≡⟨⟩
    pred (suc (in-neg x + in-pos x))
  ≡⟨ pred-suc (in-neg x + in-pos x) ⟩
    in-neg x + in-pos x
  ≡⟨ ap (in-neg x +_) (inv (Neg.neg-inv x)) ⟩
    in-neg x + (- in-neg x)
  ≡⟨ itself (in-neg x) ⟩
    zero
  ∎ 
