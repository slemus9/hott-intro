import Int.Base as Int
open import Additive

module Int.Instances where

instance
  AdditiveInt : Additive Int.Int
  AdditiveInt = record { _+_ = Int._+_ }
