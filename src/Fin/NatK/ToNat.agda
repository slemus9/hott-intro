import Nat.Add as Add
import Nat.Mul as Mul
import Nat.Less as Less
import Nat.CongruenceModK as CMK
import Fin.Incl as Incl
import Fin.NatK.Unary as Unary

open import Nat.Base
open import Fin.Base
open import Fin.NatK.Base
open import Identity
open import Function
open import Empty
open CMK.Reasoning


module Fin.NatK.ToNat where

to-nat-incl-cong : ∀ {k} -> (x y : Fin k) -> (n m : ℕ k) 
  -> to-nat (unary x n) ≡ to-nat (unary y m)
  -> incl x ≡ incl y
to-nat-incl-cong {k} x y n m eq = 
  CMK.to-eq (Incl.bounded x) (Incl.bounded y) (
      incl x
    ≡⟨ Unary.unary-incl-cong x n ⟩
      to-nat (unary x n)
    ≡⟨ CMK.when-eq k eq ⟩
      to-nat (unary y m)
    ≡⟨ CMK.sym (incl y) (to-nat (unary y m)) k (Unary.unary-incl-cong y m) ⟩ 
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
  Unary.unary-eq (Incl.injective incl-eq) (to-nat-injective n m to-nat-eq) where
    incl-eq : incl x ≡ incl y
    incl-eq = to-nat-incl-cong x y n m eq

    step1 : (suc k) * (to-nat n + 1) + incl y ≡ (suc k) * (to-nat m + 1) + incl y
    step1 = Add.rewrite-right (incl-eq) eq

    step2 : (suc k) * (to-nat n + 1) ≡ (suc k) * (to-nat m + 1)
    step2 = Add.add-both-sides-bck {(suc k) * (to-nat n + 1)} {(suc k) * (to-nat m + 1)} {incl y} step1

    to-nat-eq : to-nat n ≡ to-nat m
    to-nat-eq = Add.add-both-sides-bck {to-nat n} {to-nat m} {1} (Mul.mul-k+1-bck' step2)


to-nat-suc : ∀ {k} -> (n : ℕ k) -> to-nat (suc-ℕ n) ≡ suc (to-nat n)
to-nat-suc (constant (i x)) = Incl.incl-to-next-fin x
to-nat-suc {suc k} (constant base) rewrite Incl.incl-zero-fin (suc k) = refl
to-nat-suc (unary (i x) n) rewrite Incl.incl-to-next-fin x = refl
to-nat-suc {suc k} (unary base n) 
  rewrite Incl.incl-zero-fin (suc k)
  | to-nat-suc n
  | Add.left-suc k (suc k + suc k * to-nat n) = ap suc $ Add.commutative k (suc k + suc k * to-nat n)


{-
  Exercise 7.10.c.ii
-}
to-nat-from-nat : ∀ {k} -> ∀ a -> to-nat (from-nat {k} a) ≡ a
to-nat-from-nat {k} zero = Incl.incl-zero-fin k
to-nat-from-nat {k} (suc a) 
  rewrite to-nat-suc (from-nat {k} a) = ap suc (to-nat-from-nat a)

{-
  Exercise 7.11.c.iii

  Goal: from-nat (to-nat {suc k} n) ≡ n

  Since to-nat is injective, we get that ∀ a b -> to-nat a ≡ to-nat b -> a ≡ b

  If a = from-nat (to-nat {suc k} n) and b = n, we know that to-nat a ≡ to-nat b holds because
  of the to-nat-from-nat property:

    to-nat (from-nat (to-nat n)) ≡ to-nat n
                      to-nat n   ≡ to-nat n
  
  Hence from-nat (to-nat n) ≡ n
-}
from-nat-to-nat : ∀ {k} -> (n : ℕ (suc k)) -> from-nat (to-nat {suc k} n) ≡ n
from-nat-to-nat {k} n = to-nat-injective {suc k} (from-nat (to-nat n)) n (to-nat-from-nat (to-nat n))
