import Nat
open import Nat using (_≤_; 0≤n; s≤s)
open import Int.Properties.Suc
open import Nat.Properties.Observational.Equality using (peano8)
open import Nat.Properties.Leq as Leq
open import Int
open import DependentPair using (_<-->_; _,_)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Identity using (_≡_; refl; inv)

module Int.Properties.Abs where

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
