open import Type using (Type)
open import Identity using (_≡_; refl; trans)

module Identity.Reasoning {A : Type} where

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