open import DependentPair using (_<-->_; _×_; _,_)
open import Empty.Base using (Empty; ex-falso)
open import Type using (Type)

module Empty.Negation.Base where

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

{-
  Exercise 4.a.i
-}
taut1 : {P : Type} -> ¬ (P × (¬ P))
taut1 (p , ¬p) = ex-falso (¬p p)

{-
  Exercise 4.a.ii
-}
taut2 : {P : Type} -> ¬ (P <--> (¬ P))
taut2 (f , g) = ex-falso (f p p) where
  p = g λ p -> f p p
