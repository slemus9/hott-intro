open import Int.Def
open import Int.Properties.Suc
import Nat.Def as Nat
open import Identity.Def using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Add where

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
