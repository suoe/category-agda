import Category

module HomReasoning {c₀ c₁ ℓ} (C : Category.Category c₀ c₁ ℓ) where

open Category.Category C
open import Level

hom-refl : {a b : Obj} → {f : Hom a b} → f ≈ f
hom-refl = Category.≈-refl C

hom-sym : {a b : Obj} → {f g : Hom a b} → f ≈ g → g ≈ f
hom-sym = Category.≈-sym C

hom-trans : {a b : Obj} → {f g h : Hom a b} → f ≈ g → g ≈ h → f ≈ h
hom-trans = Category.≈-trans C

infixr  2 _∎
infixr 2 _≈⟨_⟩_ _≈⟨⟩_
infix  1 begin_

data _IsRelatedTo_ {a b : Obj} (x y : Hom a b) : Set (suc (c₀ ⊔ c₁ ⊔ ℓ ))  where
  relTo : (x≈y : x ≈ y) → x IsRelatedTo y

begin_ : {a b : Obj} {x y : Hom a b} → x IsRelatedTo y → x ≈ y 
begin relTo x≈y = x≈y

_≈⟨_⟩_ : {a b : Obj} (x : Hom a b) → {y z : Hom a b} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y≈z = relTo (hom-trans x≈y y≈z)

_≈⟨⟩_ : {a b : Obj} (x : Hom a b) → {y : Hom a b} → x IsRelatedTo y → x IsRelatedTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : {a b : Obj} (x : Hom a b) → x IsRelatedTo x
_∎ _ = relTo hom-refl

