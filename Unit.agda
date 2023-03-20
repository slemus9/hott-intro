module Unit where

  Type = Set

  data Unit : Type where
    unit : Unit

  {-
    Induction Principle
    Ctx, x : Unit |- P x type 
              Ctx |- p : P unit
    ----------------------------------------------
    Ctx, x : Unit |- ind(p, x) : (x : Unit) -> P x

    Computation rule:
    Ctx, x : Unit |- P x type
              Ctx |- p : P unit
    ------------------------------------------
    Ctx           |- ind(p, unit) = p : P unit
  -}
  ind-unit : {P : Unit -> Type} 
    -> (p : P unit)
    -> (x : Unit) -> P x
  ind-unit p unit = p

  const-unit : {A : Type}
    -> A -> Unit -> A
  const-unit a = ind-unit a 