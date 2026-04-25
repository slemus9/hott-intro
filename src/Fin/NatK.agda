open import Fin.Base
import Fin.Observational.Equality as FinEq
import Fin.Incl as Incl
open import Nat.Base
import Nat.Less as Less
import Nat.Add as Add
import Nat.Mul as Mul
import Nat.Dist as Dist
import Nat.Divides as Divides
import Nat.CongruenceModK as CMK
open import Type
open import Identity
open import Empty.Negation
open import Empty
open import DependentPair
open import Function

open CMK.Reasoning

module Fin.NatK where

data ℕ : Nat -> Type where
  constant : ∀ {k} -> Fin k -> ℕ k
  unary : ∀ {k} -> Fin k -> ℕ k -> ℕ k

to-nat : ∀ {k} -> ℕ k -> Nat
to-nat (constant x) = incl x
to-nat {k} (unary x n) = k * (to-nat n + 1) + incl x

{-
  Exercise 7.10.a
-}
empty-ℕ₀ : is-empty (ℕ 0)
empty-ℕ₀ (constant ())
empty-ℕ₀ (unary () _)

-- Observational Equality
Eq-ℕ : ∀ {k} -> ℕ k -> ℕ k -> Type
Eq-ℕ (constant x) (constant y) = Eq-Fin x y
Eq-ℕ (constant _) (unary _ _) = Empty
Eq-ℕ (unary _ _) (constant _) = Empty
Eq-ℕ (unary x n) (unary y m) = (Eq-Fin x y)  × (Eq-ℕ n m)

module Observational where

  reflex : ∀ {k} -> (n : ℕ k) -> Eq-ℕ n n
  reflex (constant x) = FinEq.reflex x
  reflex (unary x n) = FinEq.reflex x , reflex n

  eq-identity-fwd : ∀ {k} -> (n m : ℕ k) -> n ≡ m -> Eq-ℕ n m
  eq-identity-fwd n _ refl = reflex n

  eq-identity-bck : ∀ {k} -> (n m : ℕ k) -> Eq-ℕ n m -> n ≡ m 
  eq-identity-bck (constant x) (constant y) eq 
    rewrite FinEq.eq-identity-bck x y eq = refl
  eq-identity-bck (unary x n) (unary y m) (eqFin , eqℕ)
    rewrite FinEq.eq-identity-bck x y eqFin 
    | eq-identity-bck n m eqℕ = refl

  eq-identity : ∀ {k} -> (n m : ℕ k) -> (n ≡ m) <--> Eq-ℕ n m
  eq-identity n m = eq-identity-fwd n m , eq-identity-bck n m

  constant≢unary : ∀ {k} -> (x y : Fin k) -> (n : ℕ k) -> constant x ≢ unary y n
  constant≢unary x y n = eq-identity-fwd (constant x) (unary y n)

unary-eq : ∀ {k} -> 
  {x y : Fin k} -> 
  {n m : ℕ k} -> 
  (x ≡ y) -> 
  (n ≡ m) -> 
  (unary x n) ≡ (unary y m)
unary-eq refl refl = refl

unary-incl-cong : ∀ {k} -> (x : Fin k) -> (n : ℕ k) -> (incl x) ≡ (to-nat (unary x n)) mod k
unary-incl-cong {k} x n = 
  tr {Nat} {k divides_} (sym diff) (Divides.multiple k ((to-nat n + 1))) where
    diff : dist (incl x) (to-nat (unary x n)) ≡ k * (to-nat n + 1)
    diff = Dist.add-on-right (incl x) (k * (to-nat n + 1))

to-nat-incl-cong : ∀ {k} -> (x y : Fin k) -> (n m : ℕ k) 
  -> to-nat (unary x n) ≡ to-nat (unary y m)
  -> incl x ≡ incl y
to-nat-incl-cong {k} x y n m eq = 
  CMK.to-eq (Incl.bounded x) (Incl.bounded y) (
      incl x
    ≡⟨ unary-incl-cong x n ⟩
      to-nat (unary x n)
    ≡⟨ CMK.when-eq k eq ⟩
      to-nat (unary y m)
    ≡⟨ CMK.sym (incl y) (to-nat (unary y m)) k (unary-incl-cong y m) ⟩ 
      incl y
    ∎
  )

{-
  Exercise 7.10.b
-}
to-nat-injective : ∀ {k} -> (n m : ℕ k) -> to-nat n ≡ to-nat m -> n ≡ m
-- x ≡ y because incl is injective
to-nat-injective (constant x) (constant y) = ap constant ∘ Incl.injective
{- 
  if n = (constant x) , m = (unary y m) we get a contradiction because we would get that:
    incl x ≡ k * (to-nat y + 1) + incl y
  But we know that ∀ k -> incl x < k
-}
to-nat-injective {k} (constant x) (unary y m) eq
  rewrite Add.associative k (k * to-nat m) (incl y) = 
    ex-falso (Less.not-n+m<n contradiction) where
      contradiction : k + (k * to-nat m + incl y) < k
      contradiction = tr {Nat} {_< k} eq (Incl.bounded x)
{- 
  if n = (unary x n) , m = (constant y) we get a contradiction because we would get that:
    incl y ≡ k * (to-nat n + 1) + incl x
  But we know that ∀ k -> incl y < k
-}
to-nat-injective {k} (unary x n) (constant y) eq 
  rewrite Add.associative k (k * to-nat n) (incl x) = 
    ex-falso (Less.not-n+m<n contradiction) where
      contradiction : k + (k * to-nat n + incl x) < k
      contradiction = tr {Nat} {_< k} (sym eq) (Incl.bounded y)
{-
  We can show that if 
    to-nat (unary x n) ≡ to-nat (unary y m)
  then:
    incl x ≡ incl y
  and then:
    to-nat n ≡ to-nat m

  We can then use the Inductive Hypothesis to get that n ≡ m
  
  Finally, Since x ≡ y (because incl is injective) and n ≡ m, we get that:
    (unary x n) ≡ (unary y m)
-}
to-nat-injective {suc k} (unary x n) (unary y m) eq = 
  unary-eq (Incl.injective incl-eq) (to-nat-injective n m to-nat-eq) where
    incl-eq : incl x ≡ incl y
    incl-eq = to-nat-incl-cong x y n m eq

    step1 : (suc k) * (to-nat n + 1) + incl y ≡ (suc k) * (to-nat m + 1) + incl y
    step1 = Add.rewrite-right (incl-eq) eq

    step2 : (suc k) * (to-nat n + 1) ≡ (suc k) * (to-nat m + 1)
    step2 = Add.add-both-sides-bck {(suc k) * (to-nat n + 1)} {(suc k) * (to-nat m + 1)} {incl y} step1

    to-nat-eq : to-nat n ≡ to-nat m
    to-nat-eq = Add.add-both-sides-bck {to-nat n} {to-nat m} {1} (Mul.mul-k+1-bck' step2)
