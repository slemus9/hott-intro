module Empty.Def where

Type = Set

data Empty : Type where

-- There is no computation rules
ind-empty : {P : Empty -> Type}
  -> (x : Empty) -> P x
ind-empty () -- the absurd pattern

ex-falso : {A : Type} -> Empty -> A
ex-falso {A} = ind-empty {λ _ -> A}

{-
  Negation under the Propositions as Types interpretation

  Proof by negation: assume that A holds and then construct an element of the empty type
    Prove ¬ A by assuming A and deriving a contradiction

  Proof by contradiction: conclude that P holds after showing that ¬ P implies a contradiction
    ¬ ¬ P => P (double negation principle)

  The type ¬ ¬ A is equivalent to (P -> Empty) -> Empty, but we cannot construct it unless we know
  something about A. In practice, we rarely see double negation
-}
¬_ : Type -> Type
¬ A = A -> Empty

{-
  We also say that a type A is empty if it comes equiped of an
  element of type ¬ A 
-}
is-empty : Type -> Type
is-empty = ¬_
