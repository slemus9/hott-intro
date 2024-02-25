open import Fin.Base
open import Identity using (_≡_; refl; ap)
open import Nat.Base

module Fin.Next where

next-neg-two : ∀ {k} -> next (neg-two {k}) ≡ base
next-neg-two {zero} = refl
next-neg-two {suc k} = refl

pred-first : ∀ {k} -> pred (first {k}) ≡ base
pred-first {zero} = refl
pred-first {suc k} = ap skip-neg-two (pred-first {k})

{-
  base:
    next (skip-neg-two base {k})
  = next (base {suc k})
  = i (first {k})

  (i x):
    next (skip-neg-two (i x))
  = next (i (i x))
  = to-next-fin (i x)
  = i (to-next-fin x)
  = i (next x)
-}
next-skip-neg-two : ∀ {k} -> (x : Fin k) -> next (skip-neg-two x) ≡ i (next x)
next-skip-neg-two base = refl
next-skip-neg-two (i _) = refl

{-
    pred (to-next-fin (base {k}))
  = pred (base {suc k})
  = neg-two {suc k}
  = i (base {k})

    pred (to-next-fin (i x))
  = pred (i (to-next-fin x))
  = skip-neg-two (pred (to-next-fin x))
  = skip-neg-two (i x) [By Inductive Hypothesis]
  = i (i x)
-}
pred-to-next-fin : ∀ {k} -> (x : Fin k) -> pred (to-next-fin x) ≡ i x
pred-to-next-fin base = refl
pred-to-next-fin (i x) rewrite pred-to-next-fin x = refl

{-
  Exercise 7.6
-}
next-pred : ∀ {k} -> (x : Fin k) -> next (pred x) ≡ x
next-pred base = next-neg-two
next-pred (i x) rewrite next-skip-neg-two (pred x) = ap i (next-pred x)

pred-next : ∀ {k} -> (x : Fin k) -> pred (next x) ≡ x
pred-next base = pred-first
pred-next (i x) = pred-to-next-fin x
