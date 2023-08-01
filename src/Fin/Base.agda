open import Type
open import Nat
open import DependentPair

module Fin.Base where

---------------------------
-- Standard Finite Types --
---------------------------

{-
  Standard Finite Sets: {x ∈ N | x < k}

  A set of elements x ∈ A such that P x holds, is interpreted
  as the type of terms x : A equipped with an element p : P x
-}
Classical-Fin : (k : Nat) -> Type
Classical-Fin k = Σ Nat λ x -> x < k

-- Inductive definition
data Fin : Nat -> Type where
  base : ∀ {k} -> Fin (suc k)
  i : ∀ {k} -> Fin k -> Fin (suc k)

----------------
-- Operations --
----------------

-- Induction principle
ind-fin : {P : (k : Nat) -> Fin k -> Type}
  -> (∀ k -> P (suc k) base)
  -> (∀ k x -> P k x -> P (suc k) (i x))
  -> ∀ k -> ∀ x -> P k x
ind-fin p g (suc k) base = p k
ind-fin p g (suc k) (i x) = g k x (ind-fin p g k x)

-- Inclusion functions
incl : ∀ k -> Fin k -> Nat
incl (suc k) base = k
incl (suc k) (i x) = incl k x
