open import Type using (Type)
open import Nat using (Nat; zero; suc)

module Nat.Ordering where 

data _≤_ : Nat -> Nat -> Type where
  0≤n : ∀ {n} -> zero ≤ n
  s≤s : ∀ {m n} -> m ≤ n -> suc m ≤ suc n
