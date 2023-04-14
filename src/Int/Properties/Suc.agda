open import Int.Def using (Int; in-neg; in-pos; zero; suc; pred)
import Nat.Def as Nat
open import Identity.Def using (_≡_; refl)

{-
  Exercise 5.6
-}
module Int.Properties.Suc where

  suc-pred : ∀ x -> suc (pred x) ≡ x
  suc-pred (in-neg Nat.zero) = refl
  suc-pred (in-neg (Nat.suc x)) = refl
  suc-pred zero = refl
  suc-pred (in-pos Nat.zero) = refl
  suc-pred (in-pos (Nat.suc Nat.zero)) = refl
  suc-pred (in-pos (Nat.suc (Nat.suc x))) = refl

  pred-suc : ∀ x -> pred (suc x) ≡ x
  pred-suc (in-neg Nat.zero) = refl
  pred-suc (in-neg (Nat.suc Nat.zero)) = refl
  pred-suc (in-neg (Nat.suc (Nat.suc x))) = refl
  pred-suc zero = refl
  pred-suc (in-pos Nat.zero) = refl
  pred-suc (in-pos (Nat.suc x)) = refl

  pred-neg : ∀ n -> pred (in-neg n) ≡ in-neg (Nat.suc n)
  pred-neg Nat.zero = refl
  pred-neg (Nat.suc n) = refl

  suc-pos : ∀ n -> suc (in-pos n) ≡ in-pos (Nat.suc n)
  suc-pos Nat.zero = refl
  suc-pos (Nat.suc n) = refl