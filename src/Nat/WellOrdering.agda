open import Nat.Base
open import Decidable.Base
open import Type
open import Identity.Base
open import Function.Base
open import Empty.Negation
open import DependentPair
open import Coproduct

import Nat.Add as Add
import Nat.Less as Less

{-
  The Well Ordering Principle of Natural Numbers states that any non-empty subset of the Natural Numbers has a least element.
  To formulate this principle we use type families over `Nat` instead of subsets, and we try o find the minimal element m such that P(m) holds.
  Since we need to know whether P holds or not for a given number, we need P to be a decidable family.

  To find this minimal element, we require evidence that there exists an element such that P holds (meaning that the subset is not empty), 
  and we need to return the first element m such that P(m) holds. Hence, we need to define a function with the following type:

  Σ Nat P -> Σ Nat (λ m -> P m × ∀ x -> P x -> n ≤ x)
-}
module Nat.WellOrdering (P : Nat -> Type) (decide : decidable-family P) where

  {-
    Helpers to manipulate the invariant conditions of the `find-minimum-from function`
  -}
  private
    step-predicate-invariant : ∀ x n
      -> P (suc (x + n))
      -> P (suc x + n)
    step-predicate-invariant x n = 
      tr {Nat} {P} {suc (x + n)} {suc x + n} (inv $ Add.left-suc x n)

    step-bound-invariant : ∀ x
      -> ¬ (P x)
      -> (∀ y -> y < x -> ¬ (P y))
      -> ∀ y -> y < (suc x) -> ¬ (P y)
    step-bound-invariant x not-px f y l with Less.less-suc-to-leq l
    ... | inl l = f y l -- when y < x
    ... | inr eq = tr (inv eq) not-px -- when y = x

  {-
    It finds the minimum element m in the range [x, x+n] such that P(m) holds. 
    
    To better understand this function, we can start by defining a simpler version, just like we would do in
    any ordinary programming language without dependent types:

    find-minimum : Nat -> Nat -> (Nat -> Bool) -> Nat
    find-minimum x zero p    = x
    find-minimum x (suc n) p = if p x then x else find-minimum (suc x) n p

    As you can see, we are iterating from x to x + n, and we are checking whether p(x) holds on each iteration. 
    We return the first x number such that p(x) returns true (or x + n if we couldn't find any)

    Now, in order to prove that this function in fact finds the minimal number, we refine the types to express some 
    invariants. Namely:

    - P (x + n)
    - ∀ y -> y < x -> ¬ (P y)

    The first invariant is necessary because we need an upper bound such that P holds (because we require the subset to be non-empty).
    Since the recursion stops at x + n, we require evidence that P holds for this last number

    The second invariant helps us track the fact that, when transitioning to the next recursive call from x to suc(x), all elements y that are less
    than x do not fulfill the predicate P(y). This way, when reaching the base case n = 0, we have proof that that we couldn't find the minimal element
    in all the previous recursive calls
  -}
  find-minimum-from : ∀ x n
    -> P (x + n)
    -> is-lower-bound-complement P x
    -> Σ Nat (λ m -> P m × is-lower-bound-complement P m)
  find-minimum-from x zero p f = x , (p , f)
  find-minimum-from x (suc n) p f with decide x
  ... | inl px = x , (px , f) -- P x
  ... | inr not-px = find-minimum-from (suc x) n (step-predicate-invariant x n p) (step-bound-invariant x not-px f) -- ¬ (P x)

  {-
    Finds the minimum element starting from 0
  -}
  find-minimum : Σ Nat P -> Σ Nat (λ m -> P m × is-lower-bound-complement P m)
  find-minimum (n , p) = 
    find-minimum-from 
      zero 
      n 
      (tr {Nat} {P} {n} {0 + n} (inv $ Add.left-unit n) p)
      zero-is-lower-bound-complement

  well-ordering : Σ Nat P -> Σ Nat (λ m -> P m × is-lower-bound P m)
  well-ordering n with find-minimum n 
  ... | (m , (p , f)) = m , (p , lower-bound-from-complement m f)
