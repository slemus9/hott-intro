open import Empty.Def using (¬_)
open import Function.Def using (_∘_; _<==>_)
open import DependentPair.Def using (_×_; _,_)

module Empty.Properties.Negation where

Type = Set

-- Proposition 4.3.4
contrapos : {P Q : Type}
  -> (P -> Q) -> ¬ Q -> ¬ P
contrapos f notQ = notQ ∘ f

{-
  Exercise 4.3.a.i
-}
contradiction1 : {P : Type}
  -> ¬ (P × (¬ P))
contradiction1 (p , notP) = notP p

{-
  Exercise 4.3.a.ii
-}
contradiction2 : {P : Type}
  -> ¬ (P <==> (¬ P))
contradiction2 record {to = f; from = g} = notP p
  where
    p = g (λ p -> (f p) p)
    notP = f p
