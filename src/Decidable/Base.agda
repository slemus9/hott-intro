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

zero-is-lower-bound : (P : Nat -> Type) -> is-lower-bound P 0
zero-is-lower-bound P x _ = 0≤n

make-lower-bound : {P : Nat -> Type}
  -> (n : Nat)
  -> (∀ x -> x < n -> ¬ (P x))
  -> is-lower-bound P n
make-lower-bound n f x px with Less.connected x n 
... | Less.Connected.low l = ex-falso (f x l px) -- when x < n
... | Less.Connected.middle eq = Leq.when-eq (inv eq) -- when x = n
... | Less.Connected.high h = Leq.when-less h -- when n < x

find-minimum-from : {P : Nat -> Type}
  -> decidable-family P
  -> (x n : Nat)
  -> P (x + n)
  -> (∀ y -> y < x -> ¬ (P y))
  -> Σ Nat (λ m -> P m × ∀ y -> y < m -> ¬ (P y))
find-minimum-from d x zero px f with d zero 
... | inl p0 = zero , (p0 , λ _ -> ex-falso ∘ Less.not-less-than-zero) -- nothing is less than 0
... | inr not-p0 = x , (px , f)

find-minimum-from {P} d x (suc n) pxn f with d x 
... | inl px = x , (px , f)
... | inr not-px = find-minimum-from d (suc x) n step-P (step-invariant f) where
  step-P : P (suc x + n)
  step-P = tr {Nat} {P} {suc (x + n)} {suc x + n} (inv $ Add.left-suc x n) pxn

  step-invariant : (∀ y -> y < x -> ¬ (P y)) -> (∀ y -> y < (suc x) -> ¬ (P y))
  step-invariant f y l with Less.single-step l
  ... | inl l = f y l -- when y < x
  ... | inr eq = tr (inv eq) not-px -- when y = x

find-minimum : {P : Nat -> Type}
  -> decidable-family P
  -> Σ Nat P
  -> Σ Nat (λ m -> P m × ∀ y -> y < m -> ¬ (P y))
find-minimum {P} d (n , p) = 
  find-minimum-from d zero n 
    (tr {Nat} {P} {n} {0 + n} (inv $ Add.left-unit n) p) 
    (λ _ -> ex-falso ∘ Less.not-less-than-zero)

well-ordering : {P : Nat -> Type}
  -> decidable-family P
  -> Σ Nat P
  -> Σ Nat (λ m -> P m × is-lower-bound P m)
well-ordering d n with find-minimum d n 
... | (m , (p , f)) = m , (p , make-lower-bound m f)
