import Nat
open import Int
open import Int.Properties.Suc
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Neg where

pos-inv : ∀ n -> (- in-pos n) ≡ in-neg n
pos-inv n = refl

neg-inv : ∀ n -> (- in-neg n) ≡ in-pos n 
neg-inv n = refl

suc-inv : ∀ n -> (- suc n) ≡ pred (- n)
suc-inv (in-neg Nat.zero) = refl
suc-inv (in-neg (Nat.suc x)) = inv (pred-pos x)
suc-inv zero = refl
suc-inv (in-pos Nat.zero) = pred-neg Nat.zero
suc-inv (in-pos (Nat.suc x)) = inv (pred-neg (Nat.suc x))

pred-inv : ∀ x -> (- pred x) ≡ suc (- x)
{-
  suc (- in-neg zero) = suc (in-pos zero) = in-pos (suc zero)
  (- pred (in-neg zero)) = - (in-neg (suc zero)) = in-pos (suc zero)
-}
pred-inv (in-neg Nat.zero) = suc-pos Nat.zero
{-
  suc (- in-neg (suc x)) = suc (in-pos (suc x)) = in-pos (suc (suc x))
  (- pred (in-neg (suc x))) = (- in-neg (suc (suc x))) = (in-pos (suc (suc x)))
-}
pred-inv (in-neg (Nat.suc x)) = suc-pos (Nat.suc x)
pred-inv zero = refl
pred-inv (in-pos Nat.zero) = refl
{-
  suc (- in-pos (suc x)) = suc (in-neg (suc x))
  - pred (in-pos (suc x)) = - in-pos x = in-neg x
-}
pred-inv (in-pos (Nat.suc x)) = suc-neg x

distrib-+ : ∀ x y -> - (x + y) ≡ (- x) + (- y)
{-
  - (x + in-neg zero) = - pred x
  (- x) + (- in-neg zero) = (- x) + (in-pos zero) = suc (- x) 
-}
distrib-+ x (in-neg Nat.zero) = pred-inv x
distrib-+ x (in-neg (Nat.suc y)) = 
  begin
    - pred (x + in-neg y)
  ≡⟨ pred-inv (x + in-neg y) ⟩
    suc (- (x + in-neg y))
  ≡⟨ ap suc (distrib-+ x (in-neg y)) ⟩
    suc ((- x) + (- in-neg y))
  ≡⟨ ap (λ a -> suc ((- x) + a)) (neg-inv y) ⟩
    suc ((- x) + in-pos y)
  ∎
distrib-+ x zero = refl
{-
  - (x + (in-pos zero)) = - suc x
  (- x) + (- in-pos zero) = (- x) + in-neg zero = pred (- x)
-}
distrib-+ x (in-pos Nat.zero) = suc-inv x
distrib-+ x (in-pos (Nat.suc y)) = 
  begin
    - suc (x + in-pos y)
  ≡⟨ suc-inv (x + in-pos y) ⟩
    pred (- (x + in-pos y))
  ≡⟨ ap pred (distrib-+ x (in-pos y)) ⟩
    pred ((- x) + (- in-pos y))
  ≡⟨ ap (λ a -> pred ((- x) + a)) (pos-inv y) ⟩
    pred ((- x) + in-neg y)
  ∎

double-inv : ∀ x -> (- (- x)) ≡ x
double-inv (in-neg x) = refl
double-inv zero = refl
double-inv (in-pos x) = refl
