import Nat
open import Nat using (_≤_; 0≤n; s≤s)
open import Nat.Observational.Equality using (peano8)
import Nat.Leq as Leq
import Nat.Add
import Nat.Mul
open import Int.Base
open import Int.Suc
import Int.Mul
open import DependentPair using (_<-->_; _,_)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Identity using (_≡_; refl; inv; ap)
open import Identity.Reasoning

module Int.Abs where

neg-invariant : ∀ x -> abs (- x) ≡ abs x
neg-invariant (in-neg x) = refl
neg-invariant zero = refl
neg-invariant (in-pos x) = refl

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
distrib-*-pos : ∀ m n -> abs (in-pos m * in-pos n) ≡ Nat.suc m Nat.* Nat.suc n
distrib-*-pos m n
  rewrite Int.Mul.mul-pos m n
  | Nat.Add.left-suc m (Nat.suc m Nat.* n) = refl

distrib-* : ∀ x y -> abs (x * y) ≡ Nat._*_ (abs x) (abs y)
distrib-* (in-neg x) (in-neg y)
  rewrite Int.Mul.neg-by-neg x y = distrib-*-pos x y
distrib-* zero (in-neg y)
  rewrite Int.Mul.left-zero (in-neg y)
  | Nat.Mul.left-zero y = refl
distrib-* (in-pos x) (in-neg y)
  rewrite Int.Mul.right-neg-nat (in-pos x) y
  | neg-invariant (in-pos x * in-pos y) = distrib-*-pos x y
distrib-* x zero = refl
distrib-* (in-neg x) (in-pos y)
  rewrite Int.Mul.left-neg-nat x (in-pos y)
  | neg-invariant (in-pos x * in-pos y) = distrib-*-pos x y
distrib-* zero (in-pos y)
  rewrite Int.Mul.left-zero (in-pos y)
  | Nat.Mul.left-zero y = refl
distrib-* (in-pos x) (in-pos y) = distrib-*-pos x y
