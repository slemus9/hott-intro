open import Agda.Primitive using (Level)
open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (Σ; _<-->_; _×_; _,_; fst; snd)
open import Empty using (Empty; ex-falso)
open import Empty.Negation using (¬_)
open import Function using (_∘_; id; _$_)
open import Identity using (_≡_; inv; tr)
open import Nat 
open import Nat.Observational.Equality using (Eq-Nat; equiv-Eq-Nat)
open import Type using (Type; _⊔_; lsuc)
open import Unit using (Unit)
open import Fin using (Fin; Eq-Fin; [_]⟨_⟩)

import Fin.Observational.Equality as FinObsEq
import Fin.NatModK+1 as FinMod
import Nat.Add as Add
import Nat.Divides as Divides
import Nat.Dist as Dist
import Nat.Leq as Leq
import Nat.Less as Less

module Decidable.Base where

decidable : {l : Level} -> Type l -> Type l
decidable A = A ⨄ (¬ A)

decidable-family : {l1 l2 : Level} {A : Type l1} -> (P : A -> Type l2) -> Type (l1 ⊔ l2)
decidable-family P = ∀ x -> decidable (P x)

has-decidable-eq : Type -> Type
has-decidable-eq A = (x y : A) -> decidable (x ≡ y)

unit : decidable Unit
unit = inl Unit.unit

empty : decidable Empty
empty = inr id

neg : {A : Type} -> decidable A -> decidable (¬ A)
neg (inl a) = inr λ ¬a -> ex-falso (¬a a)
neg (inr ¬a) = inl ¬a

coproduct : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A ⨄ B)
coproduct (inl a) _ = inl (inl a)
coproduct (inr _) (inl b) = inl (inr b)
coproduct (inr ¬a) (inr ¬b) = inr λ where
  (inl a) -> ¬a a
  (inr b) -> ¬b b

product : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A × B)
product (inl a) (inl b) = inl (a , b)
product (inl a) (inr ¬b) = inr (¬b ∘ snd)
product (inr ¬a) (inl b) = inr (¬a ∘ fst)
product (inr ¬a) (inr _) = inr (¬a ∘ fst)

function : {A B : Type}
  -> decidable A
  -> decidable B
  -> decidable (A -> B)
function _ (inl b) = inl λ _ -> b
function (inl a) (inr ¬b) = inr λ f -> ¬b (f a)
function (inr ¬a) (inr ¬b) = inl (ex-falso ∘ ¬a)

from-bijection-fwd : {A B : Type}
  -> A <--> B
  -> decidable A
  -> decidable B
from-bijection-fwd (f , _) (inl a) = inl (f a)
from-bijection-fwd (_ , g) (inr ¬a) = inr (¬a ∘ g)

from-bijection-bck : {A B : Type}
  -> A <--> B
  -> decidable B
  -> decidable A
from-bijection-bck (_ , g) (inl b) = inl (g b)
from-bijection-bck (f , _) (inr ¬b) = inr (¬b ∘ f)

from-bijection : {A B : Type}
  -> A <--> B
  -> decidable A <--> decidable B
from-bijection a<->b = from-bijection-fwd a<->b , from-bijection-bck a<->b

to-decidable-pair : {A B : Type}
  -> decidable A
  -> (A -> decidable B)
  -> decidable (A × B)
to-decidable-pair (inl a) f = product (inl a) (f a)
to-decidable-pair (inr notA) f = inr λ { (a , _) -> notA a}

to-decidable-function : {A B : Type}
 -> decidable A
 -> (A -> decidable B)
 -> decidable (A -> B)
to-decidable-function (inl a) f = function (inl a) (f a)
to-decidable-function (inr notA) f = inl (ex-falso ∘ notA)

eq-nat : ∀ m n -> decidable (Eq-Nat m n)
eq-nat zero zero = unit
eq-nat zero (suc n) = empty
eq-nat (suc m) zero = empty
eq-nat (suc m) (suc n) = eq-nat m n

nat-has-eq : has-decidable-eq Nat
nat-has-eq m n = from-bijection-bck (equiv-Eq-Nat m n) (eq-nat m n)

eq-fin : ∀ {k} -> (x y : Fin k) -> decidable (Eq-Fin x y)
eq-fin Fin.base Fin.base = unit
eq-fin Fin.base (Fin.i _) = empty
eq-fin (Fin.i _) Fin.base = empty
eq-fin (Fin.i x) (Fin.i y) = eq-fin x y

fin-has-eq : ∀ {k} -> has-decidable-eq (Fin k)
fin-has-eq x y = from-bijection-bck (FinObsEq.eq-identity x y) (eq-fin x y)

divides-nat : ∀ d x -> decidable (d divides x)
divides-nat zero x = from-bijection-bck (Divides.zero-divides-zero x) (nat-has-eq x 0)
divides-nat (suc d) x = 
  simplify-dist 
    (from-bijection-fwd (FinMod.effectiveness d x 0) 
    (fin-has-eq [ x ]⟨ d ⟩ [ 0 ]⟨ d ⟩)) 
  where
    simplify-dist : decidable (suc d divides (dist x 0)) -> decidable (suc d divides x)
    simplify-dist rewrite Dist.right-unit x = id

{-
  Example of function definition by case analysis on a decidable predicate
-}
collatz : Nat -> Nat
collatz n with divides-nat 2 n 
... | inl holds = n /2
... | inr not-holds = 3 * n + 1

all-nat-family-from-leq : {P : Nat -> Type}
  -> decidable (∀ m x -> m ≤ x -> P x)
  -> decidable (∀ x -> P x)
all-nat-family-from-leq {P} = from-bijection-fwd (from , to) where
  from : (∀ m x -> m ≤ x -> P x) -> ∀ x -> P x
  from f x with Leq.exists-leq x
  ... | (m , leq) = f m x leq

  to : (∀ x -> P x) -> ∀ m x -> m ≤ x -> P x
  to f _ x _ = f x

is-lower-bound : (Nat -> Type) -> Nat -> Type
is-lower-bound P n = ∀ x -> P x -> n ≤ x

is-upper-bound : (Nat -> Type) -> Nat -> Type
is-upper-bound P n = ∀ x -> P x -> x ≤ n

{-
  We can also say that n is a lower bound if P(n) holds and, for all elements x < n, P(x) does not hold
-}
is-lower-bound-complement : (Nat -> Type) -> Nat -> Type
is-lower-bound-complement P n = ∀ x -> x < n -> ¬ (P x)

{-
  Zero is a lower bound for all type families over Nat
-}
zero-is-lower-bound : {P : Nat -> Type} -> is-lower-bound P 0
zero-is-lower-bound _ _ = 0≤n

zero-is-lower-bound-complement : {P : Nat -> Type} -> is-lower-bound-complement P 0
zero-is-lower-bound-complement _ = ex-falso ∘ Less.not-less-than-zero -- nothing is less than 0

lower-bound-from-complement : {P : Nat -> Type}
  -> (n : Nat)
  -> is-lower-bound-complement P n
  -> is-lower-bound P n
lower-bound-from-complement n f x px with Less.connected x n 
... | Less.Connected.low l = ex-falso (f x l px) -- when x < n
... | Less.Connected.middle eq = Leq.when-eq (inv eq) -- when x = n
... | Less.Connected.high h = Leq.when-less h -- when n < x

{-
  The Well Ordering Principle of Natural Numbers states that any non-empty subset of the Natural Numbers has a least element.
  To formulate this principle we use type families over `Nat` instead of subsets, and we try o find the minimal element m such that P(m) holds.
  Since we need to know whether P holds or not for a given number, we need P to be a decidable family.

  To find this minimal element, we require evidence that there exists an element such that P holds (meaning that the subset is not empty), 
  and we need to return the first element m such that P(m) holds. Hence, we need to define a function with the following type:

  Σ Nat P -> Σ Nat (λ m -> P m × ∀ x -> P x -> n ≤ x)
-}
module WellOrdering (P : Nat -> Type) (decide : decidable-family P) where

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
    We return the first x number such that p(x) returns true (or n if we couldn't find any)

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
