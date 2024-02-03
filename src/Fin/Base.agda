open import DependentPair
open import Empty
open import Nat
open import Type
open import Unit

module Fin.Base where

---------------------------
-- Standard Finite Types --
---------------------------

{-
  Standard Finite Sets: {x ∈ N | x < k}

  A set of elements x ∈ A such that P x holds, is interpreted
  as the type of terms x : A equipped with an element p : P x
-}
ClassicalFin : Nat -> Type
ClassicalFin k = Σ Nat λ x -> x < k

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
  -> ∀ k x -> P k x
ind-fin p g (suc k) base = p k
ind-fin p g (suc k) (i x) = g k x (ind-fin p g k x)

-- Inclusion functions
incl : ∀ {k} -> Fin k -> Nat
incl {suc k} base = k
incl (i x) = incl x

{-
  The first element of Fin (suc k) is:
    i {k} (... i {2} (i {1} (base {0})))
-}
first : ∀ {k} -> Fin (suc k)
first {zero} = base
first {suc k} = i (first {k})

{-
  to-next (i {k + n} (... i {k + 2} (i {k + 1} (base {k}))))
    = i {k + n + 1} (... i {k + 3} (i {k + 2} (base {k + 1})))
-}
to-next-fin : ∀ {k} -> Fin k -> Fin (suc k)
to-next-fin base = base
to-next-fin (i x) = i (to-next-fin x)

{-
  Successor function:

  Example: the elements of the type Fin 5 in succession are the following:
  1. i (i (i (i (base {0}))))
  2. i (i (i (base {1})))
  3. i (i (base {2}))
  4. i (base {3})
  5. base {4}

  Note the following applications of next:
  next (i (i (i base))) = i (i base)
  next (base {4}) = i (i (i (i (base {0}))))
-}
next : ∀ {k} -> Fin k -> Fin k
next base = first
next (i x) = to-next-fin x

neg-two : ∀ {k} -> Fin (suc k)
neg-two {zero} = base
neg-two {suc k} = i base

skip-neg-two : ∀ {k} -> Fin k -> Fin (suc k)
skip-neg-two base = base
skip-neg-two (i x) = i (i x)

{-
  Predecesor Function

  Examples on Fin 5

    pred $ i (base {3})
  = skip-neg-two $ pred (base {3})
  = skip-neg-two $ i (base {2})
  = i (i base {2})

    pred $ i (i base {2})
  = skip-neg-two $ pred (i base {2})
  = skip-neg-two $ skip-neg-two $ pred (base {2})
  = skip-neg-two $ skip-neg-two $ i (base {1})
  = skip-neg-two $ i $ i (base {1})
  = i $ i $ i (base {1})
-}
pred : ∀ {k} -> Fin k -> Fin k
pred base = neg-two
pred (i x) = skip-neg-two (pred x)

-- Quotient map
[_] : ∀ {k} -> Nat -> Fin (suc k)
[ zero ] = first
[ suc n ] = next [ n ]

[_]⟨_⟩ : Nat -> ∀ k -> Fin (suc k)
[ n ]⟨ k ⟩ = [_] {k} n

one : ∀ {k} -> Fin (suc k)
one = [ 1 ]

-- Observational Equality
Eq-Fin : ∀ {k} -> Fin k -> Fin k -> Type
Eq-Fin base base = Unit
Eq-Fin base (i _) = Empty
Eq-Fin (i _) base = Empty
Eq-Fin (i x) (i y) = Eq-Fin x y
