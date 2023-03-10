module Equality where

Type = Set

{-
  For any type A, and for any x of type A, the 
  constructor refl provides evidence that x ≡ x 
  (every value is equal to itself)
  The first argument to _≡_ is given by the parameter x : A, 
  while the second is given by an index in A → Set
  An equivalence relation is one which is reflexive, symmetric, and transitive.
-}
data _≡_ {A : Type} (x : A) : A → Type where
  refl : x ≡ x

infix 4 _≡_

{-
  The argument of sym has the type x ≡ y. When doing patter matching,
  this argument is instantiated with refl, which requires x and y
  to be the same. This means that we need evidence for x ≡ x, which is 
  given by refl.
  Agda know that, when pattern matching against refl, x and y must be the
  same
-}
sym : ∀ {A : Type} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Type} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Type} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Type} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Type} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

{-
  If two values are equal and a predicate holds for 
  the first value, then the predicate holds for the
  second value 
-}
subs : ∀ {A : Type} {x y : A} (P : A → Type)
  → x ≡ y
    ---------
  → P x → P y
subs P refl Px = Px

-- Nested module
module ≡-Reasoning {A : Type} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y 
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning