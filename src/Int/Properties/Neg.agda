import Nat
open import Int
open import Int.Properties.Suc using (suc-pos; suc-neg)
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Neg where

neg-inv : ∀ n -> in-neg n ≡ (- in-pos n)
neg-inv n = refl

pos-inv : ∀ n -> in-pos n ≡ (- in-neg n) 
pos-inv n = refl

suc-inv : ∀ x -> suc (- x) ≡ (- pred x)
{-
  suc (- in-neg zero) = suc (in-pos zero) = in-pos (suc zero)
  (- pred (in-neg zero)) = - (in-neg (suc zero)) = in-pos (suc zero)
-}
suc-inv (in-neg Nat.zero) = suc-pos Nat.zero
{-
  suc (- in-neg (suc x)) = suc (in-pos (suc x)) = in-pos (suc (suc x))
  (- pred (in-neg (suc x))) = (- in-neg (suc (suc x))) = (in-pos (suc (suc x)))
-}
suc-inv (in-neg (Nat.suc x)) = suc-pos (Nat.suc x)
suc-inv zero = refl
suc-inv (in-pos Nat.zero) = refl
{-
  suc (- in-pos (suc x)) = suc (in-neg (suc x))
  - pred (in-pos (suc x)) = - in-pos x = in-neg x
-}
suc-inv (in-pos (Nat.suc x)) = suc-neg x

distrib-+ : ∀ x y -> - (x + y) ≡ (- x) + (- y)
{-
  - (x + in-neg zero) = - pred x
  (- x) + (- in-neg zero) = (- x) + (in-pos zero) = suc (- x) 
-}
distrib-+ x (in-neg Nat.zero) = inv (suc-inv x)
distrib-+ x (in-neg (Nat.suc y)) = 
  begin
    - pred (x + in-neg y)
  ≡⟨ inv (suc-inv (x + in-neg y)) ⟩
    suc (- (x + in-neg y))
  ≡⟨ ap suc (distrib-+ x (in-neg y)) ⟩
    suc ((- x) + (- in-neg y))
  ≡⟨ ap (λ a -> suc ((- x) + a)) (inv (pos-inv y)) ⟩
    suc ((- x) + in-pos y)
  ∎
distrib-+ x zero = refl
{-
  - (x + (in-pos zero)) = - suc x
  (- x) + (- in-pos zero) = (- x) + in-neg zero = pred (- x)
-}
distrib-+ x (in-pos Nat.zero) = {!   !}
distrib-+ x (in-pos (Nat.suc y)) = {!   !}
