open import Function using (_∘_)
open import Nat using (Nat; zero)
open import Unit using (Unit; unit)
open import Coproduct using (_⨄_; inr; inl)

module Int where

  Type = Set

  -- Int : Type
  -- Int = Nat ⨄ (Unit ⨄ Nat)
  data Int : Type where
    in-neg : Nat -> Int
    zero : Int
    in-pos : Nat -> Int

  neg-one : Int 
  neg-one = in-neg 0

  one : Int
  one = in-pos 0

  -- Induction principle
  ind-int : {P : Int -> Type}
    -> P neg-one
    -> (∀ n -> P (in-neg n) -> P (in-neg (Nat.suc n)))
    -> P zero
    -> P one
    -> (∀ n -> P (in-pos n) -> P (in-pos (Nat.suc n)))
    -> (n : Int) -> P n
  ind-int {P} pneg1 pnegS p0 p1 pposS = go
    where
      go : (n : Int) -> P n
      go (in-neg zero) = pneg1
      go (in-neg (Nat.suc n)) = pnegS n (go (in-neg n))
      go zero = p0
      go (in-pos zero) = p1
      go (in-pos (Nat.suc n)) = pposS n (go (in-pos n)) 

  -- successor function
  suc : Int -> Int
  suc = ind-int pneg1 pnegS p0 p1 pposS
    where
      pneg1 : Int
      pneg1 = zero
      pnegS : Nat -> Int -> Int
      pnegS n _ = in-neg n
      p0 : Int
      p0 = one
      p1 : Int
      p1 = in-pos 1
      pposS : Nat -> Int -> Int
      pposS n _ = in-pos (Nat.suc (Nat.suc n)) 

  {-
    Exercise 4.1
    Predecessor
  -}
  pred : Int -> Int
  pred = ind-int pneg1 pnegS p0 p1 pposS
    where
      pneg1 : Int
      pneg1 = in-neg 1
      pnegS : Nat -> Int -> Int
      pnegS n _ = in-neg (Nat.suc (Nat.suc n))
      p0 : Int
      p0 = neg-one
      p1 : Int
      p1 = zero
      pposS : Nat -> Int -> Int
      pposS n _ = in-pos n
