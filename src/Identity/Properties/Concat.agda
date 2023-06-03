open import Identity using (_≡_; refl; concat; inv)
open import Function using (id; _$_)

module Identity.Properties.Concat where

Type = Set

left-unit : {A : Type} {x y : A}
  -> (p : x ≡ y)
  -> concat refl p ≡ p
left-unit refl = refl

right-unit : {A : Type} {x y : A}
  -> (p : x ≡ y)
  -> concat p refl ≡ p
right-unit refl = refl

assoc : {A : Type} {x y z w : A}
  -> (p : x ≡ y)
  -> (q : y ≡ z)
  -> (r : z ≡ w)
  -> concat (concat p q) r ≡ concat p (concat q r)
assoc refl q r = refl

left-inv : {A : Type} {x y : A}
  -> (p : x ≡ y)
  -> concat (inv p) p ≡ refl
left-inv refl = refl

right-inv : {A : Type} {x y : A}
  -> (p : x ≡ y)
  -> concat p (inv p) ≡ refl
right-inv refl = refl

{-
  Exercise 5.1
-}
distrib-inv : {A : Type} {x y z : A}
  -> (p : x ≡ y)
  -> (q : y ≡ z)
  -> inv (concat p q) ≡ concat (inv q) (inv p)
distrib-inv refl q = inv $ right-unit (inv q)

{-
  Exercise 5.2
-}
inv-con : {A : Type} {x y z : A}
  -> (p : x ≡ y)
  -> (q : y ≡ z)
  -> (r : x ≡ z)
  -> concat p q ≡ r -> q ≡ concat (inv p) r
inv-con refl q r = id

con-inv : {A : Type} {x y z : A}
  -> (p : x ≡ y)
  -> (q : y ≡ z)
  -> (r : x ≡ z)
  -> concat p q ≡ r -> p ≡ concat r (inv q)
con-inv p refl r rewrite right-unit p | right-unit r = id
