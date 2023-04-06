module Bool.Def where
  
Type = Set

data Bool : Type where
  true false : Bool

-- Induction principle
-- Also called if-then-else
ind-bool : {P : Bool -> Type}
  -> P true
  -> P false
  -> (b : Bool) -> P b
ind-bool onTrue _ true = onTrue
ind-bool _ onFalse false = onFalse

{-
  Exercise 4.2.a
  negation
-}
neg : Bool -> Bool
neg = ind-bool false true

{-
  Exercise 4.2.b
  conjuntion
-}
_&&_ : Bool -> Bool -> Bool
true && b = b
false && _ = false

and : Bool -> Bool -> Bool
and a b = ind-bool b false a

{-
  Exercise 4.2.c
  disjunction
-}
_||_ : Bool -> Bool -> Bool
true || _ = true
false || b = b

or : Bool -> Bool -> Bool
or a b = ind-bool true b a
