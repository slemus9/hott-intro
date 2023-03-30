open import Function using (_∘_)
open import Nat using (Nat)
open import Unit using (Unit; unit)
open import Coproduct using (_⨄_; inr; inl)

module Int where

  Type = Set

  Int : Type
  Int = Nat ⨄ (Unit ⨄ Nat)

  -- Introduction functions
  in-pos : Nat -> Int
  in-pos = inr ∘ inr

  in-neg : Nat -> Int
  in-neg = inl

  -- Basic values
  -- -1
  negOne : Int
  negOne = in-neg(0)

  -- 0
  zero : Int
  zero = inr (inl unit)

  -- 1
  one : Int
  one = in-pos(0)
