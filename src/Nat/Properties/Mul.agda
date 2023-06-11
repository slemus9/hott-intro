open import Nat using (Nat; zero; suc; _+_; _*_)
import Nat.Properties.Add as Add
open import Nat.Properties.Observational.Equality using (peano7-l; peano7-r; peano8)
open import Identity using (_≢_; _≡_; refl; ap; inv)
open import DependentPair using (_×_; _<-->_; _,_; fst; snd)
open import Function using (id; _∘_; _$_)
open import Empty using (ex-falso)
open import Coproduct using (_⨄_; inl; inr)

{-
  Exercise 5.5
-}
module Nat.Properties.Mul where

right-zero : (n : Nat) -> n * 0 ≡ 0
right-zero n = refl

left-zero : (n : Nat) -> 0 * n ≡ 0
left-zero zero = refl
left-zero (suc n) 
  rewrite Add.left-unit (0 * n) = left-zero n

-- suc n * (suc 0) = (suc n) + (n * 0)
right-unit : (n : Nat) -> n * 1 ≡ n
right-unit zero = left-zero 1
right-unit (suc n) = refl

{-
    (suc 0) * (suc n) 
  = (suc 0) + ((suc 0) * n)
  = suc (0 + ((suc 0) * n))
-}
left-unit : (n : Nat) -> 1 * n ≡ n
left-unit zero = refl
left-unit (suc n)
  rewrite Add.left-suc 0 ((suc 0) * n)
  | Add.left-unit (1 * n) = ap suc (left-unit n)

right-suc : (m n : Nat) -> m * (suc n) ≡ m + (m * n)
right-suc _ _ = refl

{-
    (suc m) * (suc n)
  = (suc m) + ((suc m) * n)
  = suc (m + (suc m) * n)
  = suc (m + ((m * n) + n))

    (m * suc n) + suc n
  = suc (m * (suc n) + n) 
  = suc ((m + m * n) + n)
-}
left-suc : (m n : Nat) -> (suc m) * n ≡ (m * n) + n
left-suc m zero
  rewrite right-zero (suc m) = refl
left-suc m (suc n)
  rewrite Add.left-suc m (suc m * n)
  | left-suc m n
  | inv (Add.assoc m (m * n) n)  = refl

{-
    m * (suc n)
  = m + m * n
  = m + n * m

  (suc n) * m
  = (n * m) + m
-}
commutative : (m n : Nat) -> m * n ≡ n * m
commutative m zero 
  rewrite left-zero m = refl
commutative m (suc n)
  rewrite left-suc n m
  | Add.commutative (n * m) m = ap (m +_) (commutative m n)

{-
    suc m * (n + k)
  = (m * (n + k)) + n + k
  = (m * n + m * k) + n + k

    suc m * n + suc m * k
  = ((m * n) + n) + (m * k) + k
-}
distrib-+-left : (m n k : Nat) -> m * (n + k) ≡ m * n + m * k
distrib-+-left zero n k
  rewrite left-zero n
  | left-zero k
  | left-zero (n + k) = refl
distrib-+-left (suc m) n k
  rewrite left-suc m (n + k)
  | left-suc m n
  | left-suc m k
  | distrib-+-left m n k
  | Add.assoc (m * n) (m * k) (n + k)
  | inv (Add.assoc (m * k) n k) 
  | Add.commutative (m * k) n 
  | Add.assoc n (m * k) k
  | inv (Add.assoc (m * n) n (m * k + k)) = refl

{-
    (m + n) * suc k
  = (m + n) + ((m + n) * k)
  = (m + n) + (m * k + n * k)

    m * (suc k) + n * (suc k)
  = (m + m * k) + (n + n * k)
-}
distrib-+-right : (m n k : Nat) -> (m + n) * k ≡ m * k + n * k
distrib-+-right m n zero = refl
distrib-+-right m n (suc k)
  rewrite distrib-+-right m n k
  | Add.assoc m n (m * k + n * k)
  | inv (Add.assoc n (m * k) (n * k))
  | Add.commutative n (m * k)
  | Add.assoc (m * k) n (n * k)
  | inv (Add.assoc m (m * k) (n + n * k)) = refl

{-
    (m * n) * suc k
  = (m * n) + ((m * n) * k)
  = (m * n) + (m * (n * k))

    m * (n * suc k)
  = m * (n + n * k)
  = m * n + m * (n * k)
-}
assoc : (m n k : Nat) -> (m * n) * k ≡ m * (n * k)
assoc m n zero = refl
assoc m n (suc k)
  rewrite distrib-+-left m n (n * k)
  | assoc m n k = refl

{-
  Exercise 6.1.a.ii
-}
mul-k+1-l : {m n k : Nat} -> m ≡ n -> m * (k + 1) ≡ n * (k + 1)
mul-k+1-l {_} {_} {zero} = id
mul-k+1-l {_} {_} {suc k} m≡n rewrite m≡n = refl

-- TODO: Can we express this more succinctly
mul-k+1-r : {m n k : Nat} -> m * (k + 1) ≡ n * (k + 1) -> m ≡ n
mul-k+1-r {zero} {zero} {k} _ = refl
mul-k+1-r {zero} {suc n} {k} rewrite left-zero k | Add.left-suc n (suc n * k) = ex-falso ∘ peano8
mul-k+1-r {suc m} {zero} {k} rewrite left-zero k | Add.left-suc m (suc m * k) = ex-falso ∘ peano8 ∘ inv
mul-k+1-r {suc m} {suc n} {k} eq
  rewrite Add.left-suc m (suc m * k)
  | left-suc m k
  | inv (Add.assoc m (m * k) k)
  | Add.left-suc n (suc n * k)
  | left-suc n k
  | inv (Add.assoc n (n * k) k) = peano7-l (mul-k+1-r {m} {n} {k} hyp2) where
    hyp1 : (m + m * k) + k ≡ (n + n * k) + k
    hyp1 = peano7-r eq

    hyp2 : m + m * k ≡ n + n * k
    hyp2 = snd (Add.add-k {m + m * k} {n + n * k} {k}) hyp1

mul-k+1 : {m n k : Nat} -> (m ≡ n) <--> (m * (k + 1) ≡ n * (k + 1))
mul-k+1 {m} {n} {k} = mul-k+1-l {m} {n} {k} , mul-k+1-r {m} {n} {k}

{-
  Exercise 6.1.b.ii
-}
either-zero-l : {m n : Nat} -> m * n ≡ 0 -> (m ≡ 0) ⨄ (n ≡ 0)
either-zero-l {zero} {n} _ = inl refl
either-zero-l {m} {zero} _ = inr refl
either-zero-l {suc m} {suc n} rewrite Add.left-suc m (suc m * n) = ex-falso ∘ peano8 ∘ inv 

either-zero-r : {m n : Nat} -> (m ≡ 0) ⨄ (n ≡ 0) -> m * n ≡ 0
either-zero-r {_} {n} (inl refl) = left-zero n
either-zero-r (inr refl) = refl

either-zero : {m n : Nat} -> (m * n ≡ 0) <--> ((m ≡ 0) ⨄ (n ≡ 0))
either-zero = either-zero-l , either-zero-r 

{-
  Exercise 6.1.b.iii
-}
both-one-l : {m n : Nat} -> m * n ≡ 1 -> (m ≡ 1) × (n ≡ 1)
both-one-l {zero} {n} rewrite left-zero n = ex-falso ∘ peano8
both-one-l {m} {zero} = ex-falso ∘ peano8
both-one-l {suc m} {suc n} eq1 = get-left eq2 , get-right eq2 where
  f : suc m + suc m * n ≡ 1 -> m + (m * n + n) ≡ zero
  f rewrite Add.left-suc m (suc m * n) | left-suc m n = peano7-r

  eq2 : m + (m * n + n) ≡ zero
  eq2 = f eq1

  get-left : m + (m * n + n) ≡ zero -> suc m ≡ 1
  get-left = peano7-l ∘ fst ∘ Add.both-zero-l

  get-right : m + (m * n + n) ≡ zero -> suc n ≡ 1
  get-right = peano7-l ∘ snd ∘ Add.both-zero-l ∘ snd ∘ Add.both-zero-l

both-one-r : {m n : Nat} -> (m ≡ 1) × (n ≡ 1) -> m * n ≡ 1
both-one-r (refl , refl) = refl

both-one : {m n : Nat} -> (m * n ≡ 1) <--> ((m ≡ 1) × (n ≡ 1))
both-one {m} {n} = both-one-l , both-one-r

{-
  Exercise 6.1.c.ii
-}
ineq-*-n+2 : {m n : Nat} -> m + 1 ≢ (m + 1) * (n + 2)
ineq-*-n+2 {zero} {n} 
  rewrite Add.left-unit 1 | left-unit (n + 2) = peano8 ∘ peano7-r
ineq-*-n+2 {suc m} {n}
  rewrite Add.left-suc (suc m) (suc (suc m) + suc (suc m) * n)
  | Add.left-suc m (suc (suc m) + suc (suc m) * n)
  | Add.left-suc (suc m) (suc (suc m) * n) = Add.ineq-+-nonzero ∘ peano7-r ∘ peano7-r 

 