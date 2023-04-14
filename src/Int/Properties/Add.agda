open import Int.Def
open import Int.Properties.Suc using (pred-neg; suc-pos)
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
  left-unit (in-neg (Nat.suc x)) = 
    begin
      pred (zero + in-neg x)
    ≡⟨ ap pred (left-unit (in-neg x)) ⟩ 
      pred (in-neg x)
    ≡⟨ pred-neg x ⟩
      in-neg (Nat.suc x)
    ∎
  left-unit zero = refl
  left-unit (in-pos Nat.zero) = refl
  left-unit (in-pos (Nat.suc x)) = 
    begin
      suc (zero + in-pos x)
    ≡⟨ ap suc (left-unit (in-pos x)) ⟩
      suc (in-pos x)
    ≡⟨ suc-pos x ⟩
      in-pos (Nat.suc x)
    ∎
