module List where

  Type = Set 

  data List (A : Type) : Type where
    nil : List A
    _::_ : A -> List A -> List A

  {-
    Exercise 4.4.a

    Induction Principle:
    Ctx, xs : List A  |- P xs type
    Ctx               |- pNil : P nil
    Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
    -----------------------------------------------------------------
    Ctx, xs : List A  |- ind-list(pNil, pCons, xs) : P xs

    Computation Rules
    Ctx, xs : List A  |- P xs type
    Ctx               |- pNil : P nil
    Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
    -----------------------------------------------------------------
    Ctx                     |- ind-list(pNil, pCons, nil) = pNil : P nil

    Ctx, xs : List A  |- P xs type
    Ctx               |- pNil : P nil
    Ctx               |- pCons : (x : A) -> (xs : List A) -> P xs -> P (x :: xs)
    -----------------------------------------------------------------
    Ctx, x : A, xs : List A |- ind-list(pNil, pCons, x :: xs) = pCons(x, xs, ind-list(pNil, pCons, xs)) : P (x :: xs)
  -}
  ind-list : {A : Type} {P : List A -> Type}
    -> P nil
    -> (∀ x -> ∀ xs -> P xs -> P (x :: xs))
    -> (xs : List A) -> P xs
  ind-list pNil _ nil = pNil
  ind-list pNil pCons (x :: xs) = pCons x xs (ind-list pNil pCons xs)

  {-
    Exercise 4.4.b
  -}
  foldr : {A B : Type}
    -> B
    -> (A -> B -> B)
    -> List A -> B
  foldr z op = ind-list z (λ x -> λ _ -> λ next -> op x next)