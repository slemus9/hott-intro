open import Type using (Type)

module Empty.Base where

data Empty : Type where

----------------
-- Operations --
----------------

-- There are no computation rules
ind-empty : {P : Empty -> Type}
  -> (x : Empty) -> P x
ind-empty () -- the absurd pattern

ex-falso : {A : Type} -> Empty -> A
ex-falso {A} = ind-empty {λ _ -> A}
