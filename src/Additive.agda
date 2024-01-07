open import Type using (Type)

module Additive where

{-
  This is just to overload the _+_ functions for types like Nat, Int or Fin.
  We may consider a better abstraction later
-}
record Additive (A : Type) : Type where
  field
    _+_ : A -> A -> A

  infixl 6  _+_

open Additive {{...}} public
