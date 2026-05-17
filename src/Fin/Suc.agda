open import Fin.Base
open import Identity using (_≡_; refl; ap)
open import Nat.Base

module Fin.Suc where

suc-fin-neg-two : ∀ {k} -> suc-fin (neg-two {k}) ≡ base
suc-fin-neg-two {zero} = refl
suc-fin-neg-two {suc k} = refl

pred-zero-fin : ∀ {k} -> pred (zero-fin {k}) ≡ base
pred-zero-fin {zero} = refl
pred-zero-fin {suc k} = ap skip-neg-two (pred-zero-fin {k})

{-
  base:
    suc-fin (skip-neg-two base {k})
  = suc-fin (base {suc k})
  = i (zero-fin {k})

  (i x):
    suc-fin (skip-neg-two (i x))
  = suc-fin (i (i x))
  = to-next-fin (i x)
  = i (to-next-fin x)
  = i (next x)
-}
suc-fin-skip-neg-two : ∀ {k} -> (x : Fin k) -> suc-fin (skip-neg-two x) ≡ i (suc-fin x)
suc-fin-skip-neg-two base = refl
suc-fin-skip-neg-two (i _) = refl

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
suc-fin-pred : ∀ {k} -> (x : Fin k) -> suc-fin (pred x) ≡ x
suc-fin-pred base = suc-fin-neg-two
suc-fin-pred (i x) rewrite suc-fin-skip-neg-two (pred x) = ap i (suc-fin-pred x)

pred-suc-fin : ∀ {k} -> (x : Fin k) -> pred (suc-fin x) ≡ x
pred-suc-fin base = pred-zero-fin
pred-suc-fin (i x) = pred-to-next-fin x
