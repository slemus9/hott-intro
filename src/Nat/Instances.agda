import Nat.Base as Nat
open import Additive

module Nat.Instances where

instance
  NatAdditive : Additive Nat.Nat
  NatAdditive = record { _+_ = Nat._+_ }
