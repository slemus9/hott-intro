import DependentPair.Identification as DP
import Fin.Incl as Incl
import Nat.Dist as Dist
import Nat.Less as Less
open import DependentPair using (_<-->_; _,_; fst)
open import Fin.Base
open import Function using (_∘_; _$_)
open import Identity using (_≡_; refl; inv; ap)
open import Nat.Base
open import Nat.Less using (<-uniq)

module Fin.Classical where

eq-clss-fwd : ∀ {k} -> (x y : ClassicalFin k) -> x ≡ y -> fst x ≡ fst y
eq-clss-fwd _ _ = ap fst

eq-clss-bck : ∀ {k} -> (x y : ClassicalFin k) -> fst x ≡ fst y -> x ≡ y
eq-clss-bck {k} (a1 , b1) (a2 , b2) eq with DP.eq-fst {Nat} {_< k} a1 a2 b1 b2 eq
... | refl rewrite (<-uniq b1 b2) = refl

{-
  Exercise 7.7.a
-}
eq-fst : ∀ {k} -> (x y : ClassicalFin k) -> (x ≡ y) <--> (fst x ≡ fst y)
eq-fst x y = eq-clss-fwd x y , eq-clss-bck x y

-- ClassicalFin versions of the Fin.base and Fin.i function
base-clss : ∀ {k} -> ClassicalFin (suc k)
base-clss {k} = k , Less.n<s

i-clss : ∀ {k} -> ClassicalFin k -> ClassicalFin (suc k)
i-clss (x , x<k) = x , Less.right-suc x<k

to-next-clss : ∀ {k} -> ClassicalFin k -> ClassicalFin (suc k)
to-next-clss (x , x<k) = suc x , s<s x<k

-- Maps between Fin and ClassicalFin
from-fin : ∀ {k} -> Fin k -> ClassicalFin k
from-fin x = incl x , Incl.bounded x

to-fin : ∀ {k} -> ClassicalFin k -> Fin k
to-fin (zero , 0<s) = first
to-fin (suc x , s<s x<k) = to-next-fin $ to-fin (x , x<k)

to-fin-base : ∀ k -> to-fin base-clss ≡ base {k}
to-fin-base zero = refl
to-fin-base (suc k) = ap to-next-fin (to-fin-base k)

{-
  base case: to-fin (i-clss (0 , 0<s)) = i first
    to-fin (i-clss (0 , 0<s))
  = to-fin (0 , Less.right-suc 0<s)
  = to-fin {suc k} (0 , 0<s)
  = first {suc k}
  = i (first {k})

  inductive case: to-fin (i-clss (suc x , s<s x<k)) = i (to-fin (suc x , s<s x<k))
  IH: to-fin (i-clss (x , x<k)) = to-fin (x , Less.right-suc x<k) = i (to-fin (x , x<k))

    i (to-fin (suc x , s<s x<k))
  = i (to-next-fin $ to-fin (x , x<k))

    to-fin (i-clss (suc x , s<s x<k))
  = to-fin (suc x , Less.right-suc (s<s x<k))
  = to-fin (suc x , s<s (Less.right-suc x<k))
  = to-next-fin $ to-fin (x , Less.right-suc x<k)
  = to-next-fin $ i (to-fin (x , x<k)) [By IH]
  = i (to-next-fin $ to-fin (x , x<k))
-}
to-fin-i : ∀ {k} -> (x : ClassicalFin k) -> to-fin (i-clss x) ≡ i (to-fin x)
to-fin-i (zero , 0<s) = refl
to-fin-i (suc x , s<s x<k) = ap to-next-fin $ to-fin-i (x , x<k)

{-
  Exercise 7.7.b.i
-}
to-fin-from-fin : ∀ {k} -> (x : Fin k) -> to-fin (from-fin x) ≡ x
to-fin-from-fin {suc k} base = to-fin-base k
to-fin-from-fin (i x) rewrite to-fin-i (from-fin x) = ap i (to-fin-from-fin x)

from-fin-i : ∀ {k} -> (x : Fin k) -> from-fin (i x) ≡ i-clss (from-fin x)
from-fin-i base = refl
from-fin-i (i x) = refl

to-fin-to-next : ∀ {k} -> (x : ClassicalFin k) -> to-fin (to-next-clss x) ≡ to-next-fin (to-fin x)
to-fin-to-next (zero , 0<s) = refl
to-fin-to-next (suc x , s<s x<k) = refl

{-
  base case: from-fin (to-next-fin (base {k})) ≡ to-next-clss (from-fin (base {k}))
    from-fin (to-next-fin (base {k}))
  = from-fin (base {suc k})
  = incl (base {suc k}) , Incl.bounded (base {suc k})
  = suc k , Less.n<s {suc k}
  = suc k , s<s Less.n<s

  inductive case: from-fin (to-next-fin (i x)) = to-next-clss (from-fin (i x))
  IH: from-fin (to-next-fin x) = to-next-clss (from-fin x)

    from-fin (to-next-fin (i x))
  = from-fin (i $ to-next-fin x)
  = i-clss (from-fin (to-next-fin x))
  = i-clss (to-next-clss (from-fin x)) [By IH]
  = i-clss (to-next-clss (incl x , Incl.bounded x))
  = i-clss (suc (incl x), s<s (Incl.bounded x))
  = (suc (incl x) , Incl.right-suc (s<s (Incl.bounded x)))
  = (suc (incl x) , s<s (Less.right-suc (Incl.bounded x)))

    to-next-clss (from-fin (i x))
  = to-next-clss (incl (i x) , Incl.bounded (i x))
  = to-next-clss (incl x , Less.right-suc (Incl.bounded x))
  = (suc (incl x) , s<s (Less.right-suc (Incl.bounded x)))
-}
from-fin-to-next : ∀ {k} -> (x : Fin k) -> from-fin (to-next-fin x) ≡ to-next-clss (from-fin x)
from-fin-to-next base = refl
from-fin-to-next (i x) rewrite from-fin-i (to-next-fin x) = ap i-clss (from-fin-to-next x)

{-
  Exercise 7.7.b.ii

  base case: from-fin (to-fin (zero , 0<s)) = (zero , 0<s)
    from-fin (to-fin (zero , 0<s))
  = from-fin first
  = (incl first , Incl.bounded first)
  = (zero , 0<s) [because incl first = 0]

  inductive case: from-fin (to-fin (suc x , s<s x<k)) ≡ (suc x , s<s x<k)
  IH: from-fin (to-fin (x , x<k)) = (x , x<k)

    from-fin (to-fin (suc x , s<s x<k))
  = from-fin (to-next-fin $ to-fin (x , x<k))
  = to-next-clss (from-fin $ to-fin (x , x<k))
  = to-next-clss (x , x<k) [By IH]
  = (suc x , s<s x<k)
-}
from-fin-to-fin : ∀ {k} -> (x : ClassicalFin k) -> from-fin (to-fin x) ≡ x
from-fin-to-fin {suc k} (zero , 0<s) = eq-clss-bck (from-fin first) (zero , 0<s) (Incl.incl-first k)
from-fin-to-fin (suc x , s<s x<k)
  rewrite from-fin-to-next (to-fin (x , x<k)) = ap to-next-clss (from-fin-to-fin (x , x<k))
