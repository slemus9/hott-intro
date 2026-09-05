open import Type
open import DependentPair.Base
open import Coproduct.Base
open import Empty.Negation.Base
open import Function.Base


module Empty.Negation.DeMorgan where

de-morgan-or : {A B : Type} -> ¬ (A ⨄ B) -> (¬ A) × (¬ B)
de-morgan-or not-or = (not-or ∘ inl) , (not-or ∘ inr)
