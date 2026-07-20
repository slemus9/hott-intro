open import Type
open import Nat.Base
open import DependentPair.Base
open import Identity.Base
open import Decidable.Base
open import Empty.Negation.Base
open import Function.Base
open import Coproduct

import Nat.Divides as Divides
import Nat.Division as Div
import Nat.WellOrdering as WellOrdering
import Nat.Leq as Leq
import Nat.Add as Add
import Nat.Mul as Mul
import Nat.Less as Less

module Nat.GreatestCommonDivisor where

is-gcd : (a b d : Nat) -> Type
is-gcd a b d = 
  ∀ x -> ((x divides a) × (x divides b)) <--> (x divides d)

gcd-divides-both : ∀ a b d
  -> is-gcd a b d
  -> (d divides a) × (d divides b)
gcd-divides-both a b d g = 
  snd (g d) (Divides.reflex d)

{-
  The property of being a greatest common divisor uniquely characterizes the greatest common divisor
-}
gcd-uniqueness : ∀ a b d d'
 -> is-gcd a b d
 -> is-gcd a b d'
 -> d ≡ d'
gcd-uniqueness a b d d' g g' = 
  Divides.antisym d d' d-div-d' d'-div-d where
    d-div-d' : d divides d'
    d-div-d' = fst (g' d) (gcd-divides-both a b d g)

    d'-div-d : d' divides d
    d'-div-d = fst (g d') (gcd-divides-both a b d' g')

{-
  Type family that we will use to define the Greatest Common Divisor in terms of the Well-Ordering Principle
-}
well-ordered-gcd : Nat -> Nat -> Nat -> Type 
well-ordered-gcd a b n = 
  a + b ≢ 0 -> (n ≢ 0) × (∀ x -> (x divides a) × (x divides b) -> x divides n)

commute-is-gcd-fwd : ∀ a b n
  -> (∀ x -> (x divides a) × (x divides b) -> x divides n)
  -> (∀ x -> (x divides b) × (x divides a) -> x divides n)
commute-is-gcd-fwd a b n f x (div-b , div-a) = 
  f x (div-a , div-b)

commute-well-ordered-gcd : ∀ a b n
  -> well-ordered-gcd a b n
  -> well-ordered-gcd b a n
commute-well-ordered-gcd a b n wo-gcd sum-not-zero rewrite Add.commutative a b = 
  fst result , commute-is-gcd-fwd a b n (snd result) where
    result : (n ≢ 0) × (∀ x -> (x divides a) × (x divides b) -> x divides n)
    result = wo-gcd sum-not-zero

commute-gcd-lower-bound : ∀ a b n
  -> is-lower-bound (well-ordered-gcd a b) n
  -> is-lower-bound (well-ordered-gcd b a) n
commute-gcd-lower-bound a b n low-bound x wo-gcd = 
  low-bound x (commute-well-ordered-gcd b a x wo-gcd)

{-
  In order to use the Well-Ordering Principle, we first need to show that the give type family is decidable
-}
well-ordered-gcd-is-decidable : ∀ a b -> decidable-family (well-ordered-gcd a b)
well-ordered-gcd-is-decidable a b n = 
  to-decidable-function sum-not-zero common-div where
    sum-not-zero : decidable (a + b ≢ 0)
    sum-not-zero = neg (eq-nat (a + b) 0)

    n-not-zero : decidable (n ≢ 0)
    n-not-zero = neg (eq-nat n 0)

    common-div-pre : decidable-family (λ x -> (x divides a) × (x divides b))
    common-div-pre x = product (divides-nat x a) (divides-nat x b)

    common-div-post : decidable-family (λ x -> x divides n)
    common-div-post x = divides-nat x n

    upper : (a + b ≢ 0) -> is-upper-bound (λ x -> (x divides a) × (x divides b)) (a + b)
    upper not-zero x (div-a , div-b) = 
      Divides.addition-to-upper-bound a b x not-zero div-a div-b

    common-div : (a + b ≢ 0) -> decidable ((n ≢ 0) × (∀ x -> (x divides a) × (x divides b) -> x divides n))
    common-div not-zero = 
      product n-not-zero (function-nat-families (a + b) common-div-pre common-div-post (upper not-zero))

{-
  We also need to show that there is an element of the type family in order to use Well-Ordering Principle
-}
sum-is-well-ordered-gcd : ∀ a b -> well-ordered-gcd a b (a + b)
sum-is-well-ordered-gcd a b not-zero = 
  (not-zero , divides-sum) where
    divides-sum : ∀ x -> (x divides a) × (x divides b) -> x divides (a + b)
    divides-sum x (div-a , div-b) = Divides.divides-x-y-then-x+y x a b div-a div-b

-- Apply and open the WellOrdering module for the well-ordered-gcd type family
open module GcdWellOrdering (a b : Nat) = 
  WellOrdering (well-ordered-gcd a b) (well-ordered-gcd-is-decidable a b)

{-
  Definition of Greatest Common Divisor in terms of the Well Ordering Principle
-}
gcd : (a b : Nat) -> Σ Nat (λ n -> (well-ordered-gcd a b n) × is-lower-bound (well-ordered-gcd a b) n) 
gcd a b = 
  well-ordering a b ((a + b) , sum-is-well-ordered-gcd a b)

when-gcd-zero-fwd : (a b n : Nat) 
  -> well-ordered-gcd a b n
  -> n ≡ 0
  -> a + b ≡ 0
when-gcd-zero-fwd a b n wo-gcd n-is-zero = 
  double-neg (eq-nat (a + b) 0) not-not-zero where
    not-not-zero : ¬ (a + b ≢ 0)
    not-not-zero not-zero = fst (wo-gcd not-zero) n-is-zero

when-gcd-zero-bck : (a b n : Nat)
  -> is-lower-bound (well-ordered-gcd a b) n
  -> a + b ≡ 0
  -> n ≡ 0
when-gcd-zero-bck a b n low-bound sum-is-zero = 
  Leq.when-n≤0 (n-leq-zero sum-is-zero n-leq-sum) where
    n-leq-sum : n ≤ a + b
    n-leq-sum = low-bound (a + b) (sum-is-well-ordered-gcd a b)

    n-leq-zero : a + b ≡ 0 -> n ≤ a + b -> n ≤ 0
    n-leq-zero eq rewrite eq = id

when-gcd-zero : (a b n : Nat)
  -> well-ordered-gcd a b n
  -> is-lower-bound (well-ordered-gcd a b) n
  -> (n ≡ 0) <--> (a + b ≡ 0)
when-gcd-zero a b n wo-gcd low-bound = 
  when-gcd-zero-fwd a b n wo-gcd , when-gcd-zero-bck a b n low-bound

when-gcd-zero-uncurry : (a b : Nat) -> (fst (gcd a b) ≡ 0) <--> ((a + b) ≡ 0)
when-gcd-zero-uncurry a b with gcd a b
... | n , (wo-gcd , low-bound) = when-gcd-zero a b n wo-gcd low-bound

-------------------------------------------------------------
-- Proving that gcd in fact fulfills the is-gcd specification
-------------------------------------------------------------

{-
  Helper module that proves that if n is the greatest common divisor of a and b, and a + b ≡ 0,
  then any x divides a, b and n
-}
module GcdWhenSumIsZero
  (a b n : Nat)
  (low-bound : is-lower-bound (well-ordered-gcd a b) n)
  (sum-is-zero : a + b ≡ 0) where

  private
    both-zero : ∀ x -> (a ≡ 0) × (b ≡ 0) -> (x divides a) × (x divides b)
    both-zero x (a-is-zero , b-is-zero) = 
      Divides.when-dividend-zero x a a-is-zero , Divides.when-dividend-zero x b b-is-zero

  divides-both : ∀ x -> (x divides a) × (x divides b)
  divides-both x = both-zero x (Add.both-zero-fwd sum-is-zero)

  divides-gcd : ∀ x -> x divides n
  divides-gcd x = Divides.when-dividend-zero x n (when-gcd-zero-bck a b n low-bound sum-is-zero)

{-
  Helper module that proves that if n is the greatest common divisor of a and b,
  then it also divides a, when a + b ≢ 0
-}
module GcdWhenSumNonZero 
  (a b n : Nat) 
  (wo-gcd : well-ordered-gcd a b n)
  (low-bound : is-lower-bound (well-ordered-gcd a b) n)
  (sum-not-zero : a + b ≢ 0) where

  private
    open Division

    {-
      We use the euclidean division between a and n to get a ≡ q * n + r, and then
      we prove that r ≡ 0 to show that n divides a
    -}
    div-a-n : Division a n
    div-a-n = Div.euclidean-div a n

    q = quotient div-a-n
    r = remainder div-a-n    
    divisor-pos = when-divisor-positive div-a-n
    
    div : a ≡ q * n + r
    div = division div-a-n

    forward : (n ≢ 0) × ∀ x -> (x divides a) × (x divides b) -> x divides n
    forward = wo-gcd sum-not-zero

    r-less-n : r < n
    r-less-n = divisor-pos (fst forward)

    x-div-q*n : ∀ x -> x divides n -> x divides (q * n)
    x-div-q*n x = (Divides.commute-mul x n q) ∘ (Divides.divides-mul x n q)

    x-div-a : ∀ x -> x divides a -> x divides (q * n + r)
    x-div-a x = tr {Nat} {x divides_} div

    {-
      We can prove that x divides r because it divides q * n as well as q * n + r (since x divides a by assumption)
    -}
    x-div-r : ∀ x -> (x divides a) × (x divides b) -> x divides r
    x-div-r x (div-a , div-b) = 
      Divides.divides-x-x+y-then-y x (q * n) r (x-div-q*n x div-n) (x-div-a x div-a) where
        div-n : x divides n
        div-n = snd forward x (div-a , div-b)

    when-r-non-zero : r ≢ 0 -> n ≤ r
    when-r-non-zero not-zero = low-bound r (λ _ -> not-zero , x-div-r)

    {-
      r is 0 because if it were different than 0, we would get that n ≤ r since n is minimal (given by the low-bound parameter),
      which contradicts the fact that r < n due to the euclidean division between a and n
    -}
    r-is-zero : r ≡ 0
    r-is-zero = double-neg (eq-nat r 0) (λ not-zero -> 
      Less.not-leq-fwd (divisor-pos (fst forward)) (when-r-non-zero not-zero))

    n-div-a : n divides a
    n-div-a rewrite div | r-is-zero | Mul.commutative q n = q , refl

  gcd-divides : ∀ x -> x divides n -> x divides a
  gcd-divides x div-n = Divides.trans x n a div-n n-div-a

{-
  Proof that (gcd a b) fulfills the is-gcd property when a + b ≡ 0
-}
gcg-is-gcd-when-sum-is-zero : (a b n : Nat)
  -> is-lower-bound (well-ordered-gcd a b) n
  -> a + b ≡ 0
  -> is-gcd a b n
gcg-is-gcd-when-sum-is-zero a b n low-bound sum-is-zero x = 
  (λ _ -> div-gcd) , λ _ -> div-both where
    div-both : (x divides a) × (x divides b)
    div-both = GcdWhenSumIsZero.divides-both a b n low-bound sum-is-zero x

    div-gcd : x divides n
    div-gcd = GcdWhenSumIsZero.divides-gcd a b n low-bound sum-is-zero x

{-
  Proof that (gcd a b) fulfills the is-gcd property when a + b ≢ 0
-}
gcd-is-gcd-when-sum-non-zero : (a b n : Nat)
  -> well-ordered-gcd a b n
  -> is-lower-bound (well-ordered-gcd a b) n
  -> a + b ≢ 0
  -> is-gcd a b n
gcd-is-gcd-when-sum-non-zero a b n  wo-gcd low-bound sum-not-zero x = 
  snd (wo-gcd sum-not-zero) x , backwards where
    x-div-a : x divides n -> x divides a
    x-div-a = GcdWhenSumNonZero.gcd-divides a b n wo-gcd low-bound sum-not-zero x

    x-div-b : x divides n -> x divides b
    x-div-b = GcdWhenSumNonZero.gcd-divides b a n 
      (commute-well-ordered-gcd a b n wo-gcd)
      (commute-gcd-lower-bound a b n low-bound)
      (sum-not-zero ∘ (trans (Add.commutative a b)))
      x

    backwards : x divides n -> (x divides a) × (x divides b)
    backwards div-n = x-div-a div-n , x-div-b div-n

{-
  Proof that (gcd a b) fulfills the is-gcd property
-}
gcd-is-gcd : (a b n : Nat)
  -> well-ordered-gcd a b n
  -> is-lower-bound (well-ordered-gcd a b) n
  -> is-gcd a b n
gcd-is-gcd a b n wo-gcd low-bound with eq-nat (a + b) 0
-- When a + b ≡ 0
... | inl sum-is-zero = gcg-is-gcd-when-sum-is-zero a b n low-bound sum-is-zero
-- When a + b ≢ 0
... | inr sum-not-zero = gcd-is-gcd-when-sum-non-zero a b n wo-gcd low-bound sum-not-zero

gcd-is-gcd-uncurry : (a b : Nat) -> is-gcd a b (fst (gcd a b))
gcd-is-gcd-uncurry a b with gcd a b
... | n , (wo-gcd , low-bound) = gcd-is-gcd a b n wo-gcd low-bound
