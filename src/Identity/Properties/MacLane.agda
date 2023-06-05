open import Type using (Type)
open import Identity using (_≡_; refl; ap; concat)
open import Identity.Properties.Concat using (assoc)

{-
  Exercise 5.4
  Mac Lane Pentagon
-}
module Identity.Properties.MacLane {A : Type} {a b c d e : A} where

alpha1 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat (concat p q) r) s ≡ concat (concat p (concat q r)) s
alpha1 p q r s = ap (λ x -> concat x s) (assoc p q r)

alpha2 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat p (concat q r)) s ≡ concat p (concat (concat q r) s)
alpha2 p q r s = assoc p (concat q r) s

alpha3 :  (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat p (concat (concat q r) s) ≡ concat p (concat q (concat r s))
alpha3 p q r s = ap (concat p) (assoc q r s)

alpha4 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat (concat p q) r) s ≡ concat (concat p q) (concat r s)
alpha4 p q r s = assoc (concat p q) r s

alpha5 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat p q) (concat r s) ≡ concat p (concat q (concat r s))
alpha5 p q r s = assoc p q (concat r s)

-- TODO: can this be expressed in another way?
commutes : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat (alpha1 p q r s) (alpha2 p q r s)) (alpha3 p q r s) ≡ concat (alpha4 p q r s) (alpha5 p q r s)
commutes refl refl refl refl = refl 
