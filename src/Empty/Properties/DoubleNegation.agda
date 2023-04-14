open import Empty using (¬_; ex-falso)
open import Function using (_∘_; _<==>_)
open import DependentPair using (_×_; _,_)
open import Coproduct using (_⨄_; inl; inr)

module Empty.Properties.DoubleNegation where

Type = Set

{-
  Exercise 4.3.b
  Double negation monad
-}
pure : {P : Type}
  -> P -> ¬ ¬ P
pure p notP = notP p

_>>=_ : {P Q : Type}
  -> ¬ ¬ P -> (P -> ¬ ¬ Q) -> ¬ ¬ Q
(dnP >>= f) notQ = dnP (λ p -> f p notQ)

map : {P Q : Type}
  -> (P -> Q) -> ¬ ¬ P -> ¬ ¬ Q
map f dnP = dnP >>= (pure ∘ f)

_=<<_ : {P Q : Type}
  -> (P -> ¬ ¬ Q) -> ¬ ¬ P -> ¬ ¬ Q
f =<< dnP = dnP >>= f

{-
  Exercise 4.3.c
  Some classical laws with double negation
-}
classic1 : {P : Type}
  -> ¬ ¬ (¬ ¬ P -> P)
classic1 notImpl = notImpl λ dnP -> ex-falso (dnP λ p -> notImpl λ _ -> p)

classic2 : {P Q : Type}
  -> ¬ ¬ (((P -> Q) -> P) -> P)
classic2 notImpl = notImpl λ f -> f λ p -> ex-falso (notImpl λ _ -> p)

classic3 : {P Q : Type}
  -> ¬ ¬ ((P -> Q) ⨄ (Q -> P))
classic3 notPlus = notPlus (inl λ p -> ex-falso (notPlus (inr λ _ -> p)))

classic4 : {P : Type}
  -> ¬ ¬ (P ⨄ (¬ P))
classic4 notEM = notEM (inr λ p -> notEM (inl p))

{-
  Exercise 4.3.d
  Some classical laws with double negation
-}
em-implies-doubleneg : {P Q : Type}
  -> P ⨄ (¬ P) -> ¬ ¬ P -> P
em-implies-doubleneg (inl p) _ = p
em-implies-doubleneg (inr notP) dnP = ex-falso (dnP notP)

classic5 : {P Q : Type}
  -> (¬ ¬ (Q -> P)) <==> (P ⨄ (¬ P) -> Q -> P)
classic5 {P} {Q} = record {to = to; from = from}
  where
    to : (¬ ¬ (Q -> P)) -> P ⨄ (¬ P) -> Q -> P
    to _ (inl p) _ = p
    to dnImpl (inr notP) q = ex-falso (dnImpl λ f -> notP (f q))

    from : (P ⨄ (¬ P) -> Q -> P) -> ¬ ¬ (Q -> P)
    from f notImpl = notImpl λ q -> f (inr λ p -> notImpl (λ _ -> p)) q

{-
  Exercise 4.3.e 
  Show that ¬ P, P -> ¬ ¬ Q, and
  ¬ ¬ P × ¬ ¬ Q are double negation stable
-}
stable1 : {P : Type}
  -> ¬ ¬ ¬ P -> ¬ P
stable1 ¬¬¬p p = ¬¬¬p λ ¬p -> ¬p p

stable2 : {P Q : Type}
  -> ¬ ¬ (P -> ¬ ¬ Q) -> P -> ¬ ¬ Q
stable2 ¬¬f p ¬q = ¬¬f λ f -> f p ¬q

stable3 : {P Q : Type}
  -> ¬ ¬ ((¬ ¬ P) × (¬ ¬ Q)) -> (¬ ¬ P) × (¬ ¬ Q)
stable3 {P} {Q} ¬¬pair = fst , snd
  where
    fst : ¬ ¬ P
    fst ¬p = ¬¬pair λ { (¬¬p , _) -> ¬¬p ¬p } 

    snd : ¬ ¬ Q
    snd ¬q = ¬¬pair λ { (_ , ¬¬q) -> ¬¬q ¬q } 
