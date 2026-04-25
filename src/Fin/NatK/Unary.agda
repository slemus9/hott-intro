import Nat.Dist as Dist
import Nat.Divides as Divides

open import Fin.Base
open import Fin.NatK.Base
open import Identity
open import Nat

module Fin.NatK.Unary where

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
