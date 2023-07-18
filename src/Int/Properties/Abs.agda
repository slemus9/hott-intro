import Nat
open import Nat using (_≤_; 0≤n; s≤s)
open import Nat.Properties.Observational.Equality using (peano8)
open import Nat.Properties.Leq as Leq
open import Nat.Properties.Mul as NatMul
open import Int
open import Int.Properties.Suc
open import Int.Properties.Add as IntAdd
open import Int.Properties.Mul as IntMul
open import DependentPair using (_<-->_; _,_)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Properties.Abs where

neg-invariant : ∀ x -> abs (- x) ≡ abs x
neg-invariant (in-neg x) = refl
neg-invariant zero = refl
neg-invariant (in-pos x) = refl

abs-suc-pos : ∀ n -> abs (suc (in-pos n)) ≡ Nat.suc (Nat.suc n)
abs-suc-pos Nat.zero = refl
abs-suc-pos (Nat.suc n) = refl

abs-pred-neg : ∀ n -> abs (pred (in-neg n)) ≡ Nat.suc (Nat.suc n)
abs-pred-neg Nat.zero = refl
abs-pred-neg (Nat.suc n) = refl

from-suc : ∀ n -> Nat.suc n ≡ abs (in-pos n)
from-suc n = refl

{-
  Exercise 6.6.i
-}
when-zero-fwd : ∀ x -> x ≡ zero -> abs x ≡ Nat.zero
when-zero-fwd _ refl = refl

when-zero-bck : ∀ x -> abs x ≡ Nat.zero -> x ≡ zero
when-zero-bck (in-neg x) = ex-falso ∘ peano8 ∘ inv
when-zero-bck zero _ = refl
when-zero-bck (in-pos x) = ex-falso ∘ peano8 ∘ inv

when-zero : ∀ x -> (x ≡ zero) <--> (abs x ≡ Nat.zero)
when-zero x = when-zero-fwd x , when-zero-bck x

{-
  Exercise 6.6.ii
-}
abs-pred : ∀ x -> abs (pred x) ≤ Nat.suc (abs x)
abs-pred (in-neg x) rewrite pred-neg x = Leq.reflex
abs-pred zero = Leq.reflex
abs-pred (in-pos Nat.zero) = 0≤n
abs-pred (in-pos (Nat.suc x)) = Leq.right-suc $ Leq.right-suc $ Leq.reflex

abs-suc : ∀ x -> abs (suc x) ≤ Nat.suc (abs x)
abs-suc (in-neg Nat.zero) = 0≤n
abs-suc (in-neg (Nat.suc x)) = Leq.right-suc $ Leq.right-suc $ Leq.reflex
abs-suc zero = Leq.reflex
abs-suc (in-pos x) rewrite suc-pos x = Leq.reflex

triangle : ∀ x y -> abs (x + y) ≤ Nat.add (abs x) (abs y)
triangle x (in-neg Nat.zero) = abs-pred x
triangle x (in-neg (Nat.suc y)) = Leq.trans (abs-pred $ x + in-neg y) (s≤s $ triangle x (in-neg y))
triangle x zero = Leq.reflex
triangle x (in-pos Nat.zero) = abs-suc x
triangle x (in-pos (Nat.suc y)) = Leq.trans (abs-suc $ x + in-pos y) (s≤s $ triangle x (in-pos y))

{-
  Exercise 6.6.iii
-}
distrib-* : ∀ x y -> abs (x * y) ≡ Nat.mul (abs x) (abs y)
distrib-* x (in-neg Nat.zero) rewrite NatMul.right-unit (abs x) = neg-invariant x
{-
    abs (x * in-neg (suc y))
  = abs (- (x + x * in-pos y))
  = abs (x + x * in-pos y)

    mul (abs x) (abs (in-neg (suc y)))
  = mul (abs x) (abs (in-neg (suc y)))
  = mul (abs x) (suc (suc y))
  = abs x + mul (abs x) * (abs (in-pos y))
  = abs x + abs (x * in-pos y)

-}
distrib-* x (in-neg (Nat.suc y)) = {!
  begin
    abs (- (x + x * in-pos y))
  ≡⟨ neg-invariant (x + x * in-pos y) ⟩
    abs (x + x * in-pos y)
  ≡⟨ ap abs (inv $ IntMul.distrib-+-left x one (in-pos y)) ⟩
    abs (x * (one + in-pos y))
  ≡⟨ ap (λ k -> abs (x * k)) (IntAdd.commutative one (in-pos y)) ⟩
    abs (x * (suc (in-pos y)))
  ∎
  !}
distrib-* x zero = {!   !}
distrib-* x (in-pos y) = {!   !}
