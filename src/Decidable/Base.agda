open import Agda.Primitive using (Level)
open import Coproduct using (_⨄_; inl; inr)
open import DependentPair using (Σ; _<-->_; _×_; _,_; fst; snd)
open import Empty using (Empty; ex-falso)
open import Empty.Negation using (¬_)
open import Function using (_∘_; id)
open import Identity using (_≡_; inv; tr; refl)
open import Nat.Base
open import Nat.Observational.Equality using (Eq-Nat; equiv-Eq-Nat)
open import Type using (Type; _⊔_; lsuc)
open import Unit using (Unit)
open import Fin using (Fin; Eq-Fin; [_]⟨_⟩)

import Fin.Observational.Equality as FinObsEq
import Fin.NatModK+1 as FinMod
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

double-neg : {A : Type} -> decidable A -> ¬ ¬ A -> A
double-neg decide-a neg with decide-a 
... | inl a = a
... | inr not-a = ex-falso (neg not-a)

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

eq-obs-nat : ∀ m n -> decidable (Eq-Nat m n)
eq-obs-nat zero zero = unit
eq-obs-nat zero (suc n) = empty
eq-obs-nat (suc m) zero = empty
eq-obs-nat (suc m) (suc n) = eq-obs-nat m n

eq-nat : has-decidable-eq Nat
eq-nat m n = from-bijection-bck (equiv-Eq-Nat m n) (eq-obs-nat m n)

less-nat : ∀ m n -> decidable (m < n)
less-nat m n with Less.connected m n 
... | Less.Connected.low lo = inl lo
... | Less.Connected.middle eq = inr (Less.when-equal eq)
... | Less.Connected.high hi = inr (Less.asym hi)

leq-nat : ∀ m n -> decidable (m ≤ n)
leq-nat m n with Less.connected m n 
... | Less.Connected.low lo = inl (Leq.when-less lo)
... | Less.Connected.middle eq = inl (Leq.when-eq eq)
... | Less.Connected.high hi = inr (Less.not-leq-fwd hi)

eq-obs-fin : ∀ {k} -> (x y : Fin k) -> decidable (Eq-Fin x y)
eq-obs-fin Fin.base Fin.base = unit
eq-obs-fin Fin.base (Fin.i _) = empty
eq-obs-fin (Fin.i _) Fin.base = empty
eq-obs-fin (Fin.i x) (Fin.i y) = eq-obs-fin x y

eq-fin : ∀ {k} -> has-decidable-eq (Fin k)
eq-fin x y = from-bijection-bck (FinObsEq.eq-identity x y) (eq-obs-fin x y)

divides-nat : ∀ d x -> decidable (d divides x)
divides-nat zero x = from-bijection-bck (Divides.zero-divides-zero x) (eq-nat x 0)
divides-nat (suc d) x = 
  simplify-dist 
    (from-bijection-fwd (FinMod.effectiveness d x 0) 
    (eq-fin [ x ]⟨ d ⟩ [ 0 ]⟨ d ⟩)) 
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

is-upper-bound-complement : (Nat -> Type) -> Nat -> Type
is-upper-bound-complement P n = ∀ x -> n < x -> ¬ (P x)

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

upper-bound-from-complement : {P : Nat -> Type}
  -> (n : Nat)
  -> is-upper-bound-complement P n
  -> is-upper-bound P n
upper-bound-from-complement n f x px with Less.connected x n 
... | Less.Connected.low l = Leq.when-less l -- when x < n
... | Less.Connected.middle eq = Leq.when-eq eq -- when x = n
... | Less.Connected.high h = ex-falso (f x h px) -- when n < x

upper-bound-to-complement : {P : Nat -> Type}
  -> (n : Nat)
  -> is-upper-bound P n
  -> is-upper-bound-complement P n
upper-bound-to-complement zero f x l px rewrite Leq.when-n≤0 (f x px) = 
  -- contradiction because nothing is less than 0
  Less.not-n<0 l
upper-bound-to-complement (suc n) f (suc x) (s<s l) psx = 
  -- contradiction because applying f to (suc x) yields x ≤ n, but we assumed that n < x
  Less.not-leq-fwd l (Leq.pred (f (suc x) psx))

nat-family-from-leq : {P : Nat -> Type} (m : Nat)
  -> decidable-family P
  -> decidable (∀ x -> m ≤ x -> P x)
  -> decidable (∀ x -> P x)
nat-family-from-leq {P} zero decide-p decide-f = 
  from-bijection-fwd (from , to) decide-f where
    from : (∀ x -> zero ≤ x -> P x) -> ∀ x -> P x
    from f x = f x 0≤n

    to : (∀ x -> P x) -> ∀ x -> zero ≤ x -> P x
    to f x _ = f x

nat-family-from-leq {P} (suc m) decide-p decide-f with decide-p zero 
... | inl p0 = result ih where
  step-down : (∀ x -> m ≤ x -> P (x + 1)) -> ∀ x -> suc m ≤ x -> P x
  step-down f zero _ = p0
  step-down f (suc x) (s≤s l) = f x l

  decide-f' : decidable (∀ x -> suc m ≤ x -> P x) -> decidable (∀ x -> m ≤ x -> P (x + 1))
  decide-f' (inl f) = inl (λ x l -> f (x + 1) (s≤s l))
  decide-f' (inr not-f) = inr (not-f ∘ step-down)

  ih : decidable (∀ x -> P (x + 1))
  ih = nat-family-from-leq m (λ x -> decide-p (x + 1)) (decide-f' decide-f)

  result : decidable (∀ x -> P (x + 1)) -> decidable (∀ x -> P x)
  result (inl f) = inl (λ { zero → p0; (suc x) → f x})
  result (inr not-f) = inr (λ f -> not-f (λ x -> f (x + 1)))

... | inr not-p0 = inr (λ f -> not-p0 (f zero))

function-nat-families : {P Q : Nat -> Type} (m : Nat)
  -> decidable-family P
  -> decidable-family Q
  -> is-upper-bound P m
  -> decidable (∀ x -> P x -> Q x)
function-nat-families {P} {Q} m decide-p decide-q up = 
  nat-family-from-leq (m + 1) decide-p-q (inl f) where
    decide-p-q : ∀ x -> decidable (P x -> Q x)
    decide-p-q x = function (decide-p x) (decide-q x)

    after-m : ∀ x -> (m + 1) ≤ x -> ¬ (P x)
    after-m (suc x) (s≤s l) = upper-bound-to-complement m up (suc x) (Less.from-leq l)

    f : ∀ x -> (m + 1) ≤ x -> P x -> Q x
    f x l = ex-falso ∘ (after-m x l)
