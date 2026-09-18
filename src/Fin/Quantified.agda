open import Type
open import Nat.Base
open import Fin.Base
open import Decidable.Base
open import DependentPair.Base
open import Coproduct.Base
open import Identity.Base
open import Function.Base
open import Empty
open import Empty.Negation

import Fin.Classical as Clss
import Nat.Less as Less

module Fin.Quantified where

{-
  Function that tries to find the first element c : { x | x < k } such that P(c) does not hold.
  To understand this function, we can first define a simpler version without dependent types:

    find : Nat -> Option Nat
    find zero = None
    find (suc k) = if P(k) then find(k) else Some k

  find(k) will try to find the first element x (such that x < k) that does not satisfy the predicate P.
  If there is no such element, we return None.

  find-any-invalid is essentially the same function, but we enrich the types to have more information about the result.
  In particular, instead of returning None, we return the evidence that ∀ x -> x < k -> P x
-}
find-any-invalid : ∀ k
  -> (P : ClassicalFin k -> Type)
  -> decidable-family P
  -> (Σ (ClassicalFin k) λ x -> ¬ (P x)) ⨄ (∀ x -> P x)

{-
  This is the inductive case of the find-any-invalid function where k is non-zero.
  It implements the following case of the find function:

  find (suc k) = if P(k) then find(k) else Some k
-}
find-any-invalid-suc : ∀ k
  -> (P : ClassicalFin (suc k) -> Type)
  -> decidable-family P
  -> P (k , Less.n<s)
  -> (Σ (ClassicalFin (suc k)) λ x -> ¬ (P x)) ⨄ (∀ x -> P x)

find-any-invalid zero P decide-p =
  -- Contradiction because nothing is less than zero
  inr λ { (_ , less) -> ex-falso (Less.not-less-than-zero less) }
find-any-invalid (suc k) P decide-p with decide-p (k , Less.n<s)
-- If P holds for k, we need to keep looking downwards
... | inl p = find-any-invalid-suc k P decide-p p
-- If P does not hold for k, we found the element
... | inr not-p = inl ((k , Less.n<s) , not-p)

find-any-invalid-suc k P decide-p p = result where
  Q : ClassicalFin k -> Type
  Q y = P (Clss.suc-clss y)

  decide-q : decidable-family Q
  decide-q y = decide-p (Clss.suc-clss y)

  q-to-p : (∀ y -> Q y) -> ∀ y -> P y
  q-to-p f (x , less) with Less.less-suc-to-leq less
  -- when x < k, we can use our assumption f : ∀ y -> Q y
  ... | inl x-less-k = transform-p (f (x , x-less-k)) where
    transform-p : P (Clss.suc-clss (x , x-less-k)) -> P (x , less)
    transform-p rewrite Less.<-uniq (Less.trans x-less-k Less.n<s) less  = id
  -- when x = k, we can use our assumption p : P (k , Less.n<s)
  ... | inr x-eq-k = transform-p p where
    transform-p : P (k , Less.n<s) -> P (x , less)
    transform-p rewrite x-eq-k | Less.<-uniq Less.n<s less = id

  result : (Σ (ClassicalFin (suc k)) λ x -> ¬ (P x)) ⨄ (∀ x -> P x)
  result = case (find-any-invalid k Q decide-q) of λ
    { (inl (y , not-q)) -> inl (Clss.suc-clss y , not-q)
    ; (inr not-found) -> inr (q-to-p not-found)
    }

{-
  Proves that, if not all x : ClassicalFin(k) satisfy the predicate P, then there exists an element y such that ¬P(y).
  To do this, we just try to search in the range [0..k] the first natural number n for which P(n : Nat, l : n < k) does not hold
-}
not-forall-classic : {k : Nat} {P : ClassicalFin k -> Type}
  -> decidable-family P
  -> ¬ (∀ x -> P x)
  -> Σ (ClassicalFin k) λ x -> ¬ (P x)
not-forall-classic {k} {P} decide not-all with find-any-invalid k P decide
-- We found an element such that P does not hold
... | inl found = found

-- We didn't find an element such that P does not hold, but it contradicts our assumption that there is at least one of such elements
... | inr not-found = ex-falso (not-all not-found)

{-
  Exercise 8.3

  If not all x : Fin(k) satisfy the predicate P, then there exists an element y such that ¬P(y).
  It was easier to reason about it in term the classical interpretation of Fin(k):

    {x | x < k}

  If we can prove it in terms of {x | x < k}, then it must also be true for Fin k since both types are isomorphic
-}
not-forall : {k : Nat} {P : Fin k -> Type}
  -> decidable-family P
  -> ¬ (∀ x -> P x)
  -> Σ (Fin k) λ x -> ¬ (P x)
not-forall {k} {P} decide-p not-all-fin = exists-fin where
  Q : ClassicalFin k -> Type
  Q y = P (Clss.to-fin y)

  q-to-p : (∀ y -> Q y) -> ∀ x -> P x
  q-to-p f x rewrite inv (Clss.to-fin-from-fin x) = f (Clss.from-fin x)

  decide-q : decidable-family Q
  decide-q y = decide-p (Clss.to-fin y)

  exists-classic : Σ (ClassicalFin k) λ y -> ¬ (Q y)
  exists-classic = not-forall-classic decide-q (not-all-fin ∘ q-to-p)

  exists-fin : Σ (Fin k) λ x -> ¬ (P x)
  exists-fin = Clss.to-fin (fst exists-classic) , snd exists-classic
