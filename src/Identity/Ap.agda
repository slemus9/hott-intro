open import Type using (Type)
open import Identity.Base using (_≡_; refl; refl-of; ap; inv; concat)
open import Function.Base using (id; _∘_)

module Identity.Ap where

ap-id : {A : Type} {x y : A}
  -> (p : x ≡ y)
  -> ap id p ≡ p
ap-id refl = refl

ap-comp : {A B C : Type} {x y : A}
  -> (g : B -> C)
  -> (f : A -> B)
  -> (p : x ≡ y)
  -> ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp g f refl = refl

ap-refl : {A B : Type}
  -> (f : A -> B)
  -> (x : A)
  -> ap f (refl-of x)  ≡ (refl-of (f x))
ap-refl f x = refl

ap-inv : {A B : Type} {x y : A}
  -> (f : A -> B)
  -> (p : x ≡ y)
  -> ap f (inv p) ≡ inv (ap f p)
ap-inv f refl = refl

ap-concat : {A B : Type} {x y z : A}
  -> (f : A -> B)
  -> (p : x ≡ y)
  -> (q : y ≡ z)
  -> ap f (concat p q) ≡ concat (ap f p) (ap f q)
ap-concat f refl q = refl
