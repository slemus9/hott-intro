open import Int using (in-neg; in-pos; -_)
open import Identity using (_≡_; refl)

module Int.Properties.Neg where

neg-inv : ∀ n -> in-neg n ≡ (- in-pos n)
neg-inv n = refl

pos-inv : ∀ n -> in-pos n ≡ (- in-neg n) 
pos-inv n = refl
