import Nat
open import Int
open import Int.Properties.Suc
import Int.Properties.Neg as Neg
import Int.Properties.Add as Add
import Int.Properties.Minus as Minus
open import Identity using (_≡_; refl; inv; ap; trans)
open import Identity.Reasoning
open import Function using (_$_; _∘_)

module Int.Properties.Mul where

{-
  Exercise 5.8.a
-}
right-unit : ∀ x -> x * one ≡ x
right-unit x = refl

left-unit : ∀ x -> one * x ≡ x
left-unit (in-neg Nat.zero) = refl
{-
    one * in-neg (suc x)
  = - (one + (one * in-pos x))
  = - (one + in-pos x) [I.H]
  = - (in-pos zero + in-pos x)
  = - (in-pos x + in-pos zero)
  = - (suc (in-pos x))
  = - in-pos (suc x)
  = in-neg (suc x)
-}
left-unit (in-neg (Nat.suc x))
  rewrite left-unit (in-pos x)
  | Add.commutative (in-pos 0) (in-pos x)
  | suc-pos x
  | Neg.pos-inv x = refl
left-unit zero = refl
left-unit (in-pos Nat.zero) = refl
left-unit (in-pos (Nat.suc x))
  rewrite left-unit (in-pos x)
  | Add.commutative (in-pos 0) (in-pos x)
  | suc-pos x = refl

right-zero : ∀ x -> x * zero ≡ zero
right-zero x = refl

left-zero : ∀ x -> zero * x ≡ zero
left-zero (in-neg Nat.zero) = refl
left-zero (in-neg (Nat.suc x)) rewrite left-zero (in-pos x) = refl
left-zero zero = refl
left-zero (in-pos Nat.zero) = refl
left-zero (in-pos (Nat.suc x)) rewrite left-zero (in-pos x) = refl

{-
  Exercise 5.8.b

  predecessor and successor laws
-}
right-pred : ∀ x y -> x * pred y ≡ x * y - x
right-pred x (in-neg Nat.zero) = Neg.distrib-+ x x
{-
    x * pred (in-neg (suc y))
  = x * in-neg (suc (suc y))
  = - (x + x * in-pos (suc y))
  = - (x + (x + x * in-pos y))
  = (- x) + (x + x * in-pos y)

    x * (in-neg (suc y)) - x
  = (- (x + x * in-pos y)) - x
-}
right-pred x (in-neg (Nat.suc y))
  rewrite Neg.distrib-+ x (x + x * in-pos y)
  | Minus.left-neg x (- (x + x * in-pos y)) = refl
right-pred x zero = inv (Add.left-unit (- x))
{-
  x * pred (in-pos zero) = x * zero = zero
  x * (in-pos zero) - x = x - x
-}
right-pred x (in-pos Nat.zero) = inv (Minus.itself x)
{-
  x * pred (in-pos (Nat.suc y)) = x * in-pos y
  (x + x * in-pos (suc y)) - x
-}
right-pred x (in-pos (Nat.suc y)) 
  rewrite pred-pos y | Minus.add-zero-ends x (x * in-pos y) = refl

left-pred : ∀ x y -> pred x * y ≡ x * y - y
left-pred x (in-neg Nat.zero) 
  rewrite Neg.distrib-+ x (in-neg Nat.zero) = refl
{-
    pred x * in-neg (suc y)
  = - (pred x + (pred x * in-pos y))
  = - (pred x + (x * in-pos y - in-pos y)) [I.H]
  = (- pred x) + (- (x * in-pos y - in-pos y))
  = suc (- x) + (in-pos y - x * in-pos y)
  = suc (- x + in-pos y - x * in-pos y)

    x * in-neg (suc y) - in-neg (suc y)
  = x * in-neg (suc y) + in-pos (suc y)
  = suc (x * in-neg (suc y) + in-pos y)
  = suc (- (x + x * in-pos y) + in-pos y) 
-}
left-pred x (in-neg (Nat.suc y))
  rewrite left-pred x (in-pos y) 
  | Neg.distrib-+ (pred x) (x * in-pos y - in-pos y) 
  | Neg.pred-inv x 
  | Add.suc-left (- x) (- (x * in-pos y - in-pos y))
  | Neg.distrib-+ (x * in-pos y) (in-neg y)
  | inv (Add.assoc (- x) (- (x * in-pos y)) (in-pos y))
  | Neg.distrib-+ x (x * in-pos y)  = refl
left-pred x zero = refl
left-pred x (in-pos Nat.zero) = refl
left-pred x (in-pos (Nat.suc y))
  rewrite left-pred x (in-pos y)
  | Add.pred-left x (x * in-pos y + in-neg y)
  | Add.assoc x (x * in-pos y) (in-neg y) = refl

right-neg : ∀ x y -> x * (- y) ≡ (- (x * y))
right-neg x (in-neg Nat.zero) = inv $ Neg.double-inv x
right-neg x (in-neg (Nat.suc y)) = inv $ Neg.double-inv (x + x * in-pos y)
right-neg x zero = refl
right-neg x (in-pos Nat.zero) = refl
right-neg x (in-pos (Nat.suc y)) = refl

right-neg-nat : ∀ x n -> x * in-neg n ≡ (- (x * in-pos n))
right-neg-nat x n = begin
    x * in-neg n
  ≡⟨ ap (x *_) (inv $ Neg.pos-inv n) ⟩
    x * (- (in-pos n))
  ≡⟨ right-neg x (in-pos n) ⟩
    (- (x * in-pos n))
  ∎

right-suc : ∀ x y -> x * suc y ≡ x * y + x
{-
  x * suc (in-neg zero) = x * 0 = 0
  x * in-neg zero + x = - x + x = 0
-}
right-suc x (in-neg Nat.zero) 
  rewrite Minus.left-neg x x
  | Minus.itself x = refl
{-
  x * suc (in-neg (suc y)) = x * in-neg y
  x * (in-neg (suc y)) + x = - (x + x * in-pos y) + x = (- x) + (- (x * in-pos)) + x
-}
right-suc x (in-neg (Nat.suc y))
  rewrite suc-neg y 
  | Neg.distrib-+ x (x * in-pos y) 
  | Add.swap-left (- x) (- (x * in-pos y)) x
  | Add.left-inv x = right-neg-nat x y
right-suc x zero = inv (Add.left-unit x)
right-suc x (in-pos Nat.zero) = refl
{-
    x * suc (in-pos (suc y)) 
  = x * in-pos (suc (suc y)) 
  = x + x * in-pos (suc y)
  = x + (x + x * in-pos y)
  
  x * in-pos (suc y) + x = x + x * in-pos y + x
-}
right-suc x (in-pos (Nat.suc y)) = inv (Add.swap-right x (x * in-pos y) x)

left-suc : ∀ x y -> suc x * y ≡ x * y + y
left-suc x (in-neg Nat.zero) = Neg.suc-inv x
{-
    suc x * in-neg (suc y)
  = - (suc x + (suc x * in-pos y))
  = - (suc x + (x * in-pos y + in-pos y))
  = - (suc (x + (x * in-pos y + in-pos y)))
  = pred (- (x + (x * in-pos y + in-pos y)))

    x * (in-neg (suc y)) + in-neg (suc y)
  = - (x + x * in-pos y) + in-neg (suc y)
  = pred ((- (x + x * in-pos y)) + in-neg y)
-}
left-suc x (in-neg (Nat.suc y))
  rewrite left-suc x (in-pos y)
  | Add.suc-left x (x * in-pos y + in-pos y)
  | Neg.suc-inv (x + (x * in-pos y + in-pos y))
  | inv (Add.assoc x (x * in-pos y) (in-pos y))
  | Neg.distrib-+ (x + x * in-pos y) (in-pos y) = refl
left-suc x zero = refl
left-suc x (in-pos Nat.zero) = refl
left-suc x (in-pos (Nat.suc y))
  rewrite left-suc x (in-pos y)
  | Add.suc-left x (x * in-pos y + in-pos y)
  | Add.assoc x (x * in-pos y) (in-pos y)  = refl

{-
  Exercise 5.8.c
  Distributes over addition
-}
distrib-+-left : ∀ x y z -> x * (y + z) ≡ x * y + x * z
distrib-+-left x y (in-neg Nat.zero) = right-pred x y
distrib-+-left x y (in-neg (Nat.suc z)) =
  begin
    x * pred (y + in-neg z)
  ≡⟨ right-pred x (y + in-neg z) ⟩
    x * (y + in-neg z) - x
  ≡⟨ ap (_- x) $ distrib-+-left x y (in-neg z) ⟩
    x * y + x * in-neg z - x
  ≡⟨ Add.swap-right (x * y) (x * in-neg z) (- x) ⟩
    x * y + ((- x) + (x * in-neg z))
  ≡⟨ ap (λ k -> x * y + ((- x) + k)) $ right-neg-nat x z ⟩
    x * y + ((- x) + (- (x * in-pos z)))
  ≡⟨ ap (x * y +_) (inv $ Neg.distrib-+ x (x * in-pos z)) ⟩
    x * y + (- (x + x * in-pos z))
  ∎
distrib-+-left x y zero = refl
distrib-+-left x y (in-pos Nat.zero) = right-suc x y
distrib-+-left x y (in-pos (Nat.suc z)) = 
  begin
    x * suc (y + in-pos z)
  ≡⟨ right-suc x (y + in-pos z) ⟩
    x * (y + in-pos z) + x
  ≡⟨ ap (_+ x) $ distrib-+-left x y (in-pos z) ⟩ 
    x * y + x * in-pos z + x
  ≡⟨ Add.swap-right (x * y) (x * in-pos z) x ⟩
    x * y + (x + x * in-pos z)
  ∎

distrib-+-right : ∀ x y z -> (x + y) * z ≡ x * z + y * z
distrib-+-right x y (in-neg Nat.zero) = Neg.distrib-+ x y
distrib-+-right x y (in-neg (Nat.suc z))
  rewrite distrib-+-right x y (in-pos z)
  | inv $ Neg.distrib-+ (x + x * in-pos z) (y + y * in-pos z)
  | Add.assoc x y (x * in-pos z + y * in-pos z)
  | inv $ Add.swap-left (x * in-pos z) y (y * in-pos z)
  | Add.assoc (x * in-pos z) y (y * in-pos z)
  | Add.assoc x (x * in-pos z) (y + y * in-pos z) = refl
distrib-+-right x y zero = refl
distrib-+-right x y (in-pos Nat.zero) = refl
distrib-+-right x y (in-pos (Nat.suc z))
  rewrite distrib-+-right x y (in-pos z)
  | Add.assoc x y (x * in-pos z + y * in-pos z)
  | inv $ Add.swap-left (x * in-pos z) y (y * in-pos z)
  | Add.assoc (x * in-pos z) y (y * in-pos z) = inv $ Add.assoc x (x * in-pos z) (y + y * in-pos z)

left-neg : ∀ x y -> (- x) * y ≡ (- (x * y))
left-neg x (in-neg Nat.zero) = refl
left-neg x (in-neg (Nat.suc y)) = begin
    - ((- x) + (- x) * in-pos y)
  ≡⟨⟩
    - ((- x) * one + (- x) * in-pos y)
  ≡⟨ ap -_ (inv $ distrib-+-left (- x) one (in-pos y)) ⟩
    - (- x * (one + in-pos y))
  ≡⟨ ap (λ k -> - ((- x) * k)) (Add.commutative one (in-pos y)) ⟩
    - (- x * suc (in-pos y))
  ≡⟨ ap -_ (right-suc (- x) (in-pos y)) ⟩ 
    - (- x * in-pos y - x)
  ≡⟨ ap (λ k -> - (k - x)) (left-neg x (in-pos y)) ⟩
    - ((- (x * in-pos y)) - x)
  ≡⟨ ap -_ (inv $ Neg.distrib-+ (x * in-pos y) x) ⟩
    - (- (x * in-pos y + x))
  ≡⟨ ap (-_ ∘ -_) (Add.commutative (x * in-pos y) x)⟩
    - (- (x + x * in-pos y))
  ∎
left-neg x zero = refl
left-neg x (in-pos Nat.zero) = refl
left-neg x (in-pos (Nat.suc y)) = begin
    (- x) + (- x) * in-pos y
  ≡⟨⟩
    (- x) * one + (- x) * in-pos y
  ≡⟨ inv $ distrib-+-left (- x) one (in-pos y) ⟩
    (- x) * (one + in-pos y)
  ≡⟨ ap ((- x) *_) (Add.commutative one (in-pos y)) ⟩
    (- x) * suc (in-pos y)
  ≡⟨ right-suc (- x) (in-pos y) ⟩
    (- x) * in-pos y - x
  ≡⟨ ap (_- x) (left-neg x (in-pos y)) ⟩
    (- (x * in-pos y)) - x
  ≡⟨ inv $ Neg.distrib-+ (x * in-pos y) x ⟩
    - (x * in-pos y + x)
  ≡⟨ ap -_ (Add.commutative (x * in-pos y) x) ⟩
    - (x + x * in-pos y)
  ∎

left-neg-nat : ∀ n x -> in-neg n * x ≡ (- (in-pos n * x))
left-neg-nat n x = begin
    in-neg n * x
  ≡⟨ ap (_* x) (inv $ Neg.pos-inv n) ⟩
    (- (in-pos n)) * x
  ≡⟨ left-neg (in-pos n) x ⟩
    (- (in-pos n * x))
  ∎

{-
  Exercise 5.8.d
  Associativity and Commutativity
-}
assoc : ∀ x y z -> x * y * z ≡ x * (y * z)
assoc x y (in-neg Nat.zero) = inv (right-neg x y)
assoc x y (in-neg (Nat.suc z))
  rewrite assoc x y (in-pos z)
  | inv $ distrib-+-left x y (y * in-pos z) = inv $ right-neg x (y + y * in-pos z)
assoc x y zero = refl
assoc x y (in-pos Nat.zero) = refl
assoc x y (in-pos (Nat.suc z))
  rewrite assoc x y (in-pos z) = inv $ distrib-+-left x y (y * in-pos z)

commutative : ∀ x y -> x * y ≡ y * x
commutative x (in-neg Nat.zero)
  rewrite left-neg-nat Nat.zero x | left-unit x = refl
commutative x (in-neg (Nat.suc y)) = inv (begin
    in-neg (Nat.suc y) * x
  ≡⟨ left-neg-nat (Nat.suc y) x ⟩
    - (in-pos (Nat.suc y) * x)
  ≡⟨ ap (λ k -> - (k * x)) (inv $ suc-pos y) ⟩
    - (suc (in-pos y) * x)
  ≡⟨ ap -_ $ left-suc (in-pos y) x ⟩
    - (in-pos y * x + x)
  ≡⟨ ap (λ k -> - (k + x)) $ commutative (in-pos y) x ⟩
    - (x * in-pos y + x)
  ≡⟨ ap -_ $ Add.commutative (x * in-pos y) x ⟩
    - (x + x * in-pos y)
  ∎)
commutative x zero = inv $ left-zero x
commutative x (in-pos Nat.zero) = inv $ left-unit x
commutative x (in-pos (Nat.suc y)) = inv (begin
    in-pos (Nat.suc y) * x
  ≡⟨ ap (_* x) (inv $ suc-pos y) ⟩
    suc (in-pos y) * x
  ≡⟨ left-suc (in-pos y) x ⟩
    in-pos y * x + x
  ≡⟨ ap (_+ x) $ commutative (in-pos y) x ⟩
    x * in-pos y + x
  ≡⟨ Add.commutative (x * in-pos y) x ⟩
    x + x * in-pos y
  ∎)
