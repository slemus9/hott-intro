open import Identity.Def using (_≡_; refl; concat)
open import Identity.Properties.Concat using (assoc)

{-
  Exercise 5.4
  Mac Lane Pentagon
-}
module Identity.Properties.MacLane {A : Set} {a b c d e : A} where

Type = Set

alpha1 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat (concat p q) r) s ≡ concat (concat p (concat q r)) s
alpha1 p q r s rewrite assoc p q r = refl

alpha2 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat p (concat q r)) s ≡ concat p (concat (concat q r) s)
alpha2 p q r s rewrite assoc p (concat q r) s = refl

alpha3 :  (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat p (concat (concat q r) s) ≡ concat p (concat q (concat r s))
alpha3 p q r s rewrite assoc q r s = refl

alpha4 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat (concat p q) r) s ≡ concat (concat p q) (concat r s)
alpha4 p q r s rewrite assoc (concat p q) r s = refl

alpha5 : (p : a ≡ b)
  -> (q : b ≡ c)
  -> (r : c ≡ d)
  -> (s : d ≡ e)
  -> concat (concat p q) (concat r s) ≡ concat p (concat q (concat r s))
alpha5 p q r s rewrite assoc p q (concat r s) = refl

-- We need to generalize the Identity type to higher universes
-- commutes : (p : a ≡ b)
--   -> (q : b ≡ c)
--   -> (r : c ≡ d)
--   -> (s : d ≡ e)
--   -> concat (concat (alpha1 p q r s) (alpha2 p q r s)) (alpha3 p q r s) ≡ concat (alpha4 p q r s) (alpha5 p q r s)
-- commutes p q r s = {!   !}
