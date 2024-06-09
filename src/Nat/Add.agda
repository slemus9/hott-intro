open import Type using (Type)
open import Nat.Base using (Nat; zero; suc; ind-nat; _+_)
open import Nat.Observational.Equality using (peano7-bck; peano8)
open import Identity using (_≡_; _≢_; refl; ap; trans; inv)
open import DependentPair using (_×_; _<-->_; _,_; snd)
open import Function using (id; _$_; _∘_)
open import Empty using (ex-falso)

module Nat.Add where

right-unit : (n : Nat) -> n + 0 ≡ n
right-unit _ = refl

left-unit : (n : Nat) -> 0 + n ≡ n
left-unit = ind-nat refl λ _ p -> ap suc p

-- m + suc n = suc (m + n)
right-suc : (m n : Nat) -> m + suc n ≡ suc (m + n)
right-suc m n = refl

-- suc m + suc n = suc (suc m + n)
-- suc (m + suc n) = suc (suc (m + n))
left-suc : (m n : Nat) -> suc m + n ≡ suc (m + n)
left-suc m = ind-nat p0 pSuc
  where
    p0 : suc m + 0 ≡ suc (m + 0)
    p0 = refl

    pSuc : (n : Nat) -> suc m + n ≡ suc (m + n) -> suc m + suc n ≡ suc (m + suc n)
    pSuc n p = ap suc p

{-
  (m + n) + suc k = suc ((m + n) + k)
  m + (n + suc k) = m + suc (n + k) = suc (m + (n + k))
-}
associative : (m n k : Nat) -> (m + n) + k ≡ m + (n + k)
associative m n = ind-nat p0 pSuc
  where
    P : Nat -> Type
    P k = (m + n) + k ≡ m + (n + k)

    p0 : P 0
    p0 = refl

    pSuc : (k : Nat) -> P k -> P (suc k)
    pSuc k p = ap suc p

{-
  m + suc n = suc (m + n)
  suc n + m = suc (m + n)
-}
commutative : (m n : Nat) -> m + n ≡ n + m
commutative m zero
  rewrite left-unit m = refl
commutative m (suc n)
  rewrite left-suc n m = ap suc (commutative m n)

{-
  Exercise 6.1.a.i
-}
add-both-sides-fwd : {m n k : Nat} -> m ≡ n -> m + k ≡ n + k
add-both-sides-fwd {_} {_} {zero} = id
add-both-sides-fwd {_} {_} {suc k} m≡n rewrite m≡n = refl

add-both-sides-fwd' : {m n k : Nat} -> m ≡ n -> k + m ≡ k + n
add-both-sides-fwd' {m} {n} {k} rewrite commutative k m | commutative k n = add-both-sides-fwd {m}

add-both-sides-bck : {m n k : Nat} -> m + k ≡ n + k -> m ≡ n
add-both-sides-bck {_} {_} {zero} = id
add-both-sides-bck {_} {_} {suc k} = add-both-sides-bck ∘ peano7-bck

add-both-sides-bck' : {m n k : Nat} -> k + m ≡ k + n -> m ≡ n
add-both-sides-bck' {m} {n} {k} rewrite commutative k m | commutative k n = add-both-sides-bck {m}

add-both-sides : {m n k : Nat} -> (m ≡ n) <--> (m + k ≡ n + k)
add-both-sides = add-both-sides-fwd , add-both-sides-bck

{-
  Exercise 6.1.b.i
-}
both-zero-fwd : {m n : Nat} -> m + n ≡ 0 -> (m ≡ 0) × (n ≡ 0)
both-zero-fwd {zero} {n} eq = refl , trans (inv $ left-unit n) eq
both-zero-fwd {m} {zero} eq = eq , refl
both-zero-fwd {suc m} {suc n} = ex-falso ∘ peano8 ∘ inv

both-zero-bck : {m n : Nat} -> (m ≡ 0) × (n ≡ 0) -> m + n ≡ 0
both-zero-bck (refl , refl) = refl

both-zero : {m n : Nat} -> (m + n ≡ 0) <--> ((m ≡ 0) × (n ≡ 0))
both-zero = both-zero-fwd , both-zero-bck

{-
  Exercise 6.1.c.i
-}
ineq-+-nonzero : ∀ {m n} -> m ≢ m + (n + 1)
ineq-+-nonzero {suc m} {n}
  rewrite left-suc m n = ineq-+-nonzero ∘ peano7-bck
