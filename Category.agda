module Category where

open import Level
open import Relation.Binary
open Setoid renaming (_≈_ to equaloid)
open import Function using (flip)

record Category (c₀ c₁ ℓ : Level) : Set (suc (c₀ ⊔ c₁ ⊔ ℓ)) where
  infixr 9 _∘_
  infix 4 _≈_

  field
    Obj : Set c₀
    Homsetoid : Obj → Obj → Setoid c₁ ℓ

  Hom : Obj → Obj → Set c₁
  Hom a b = Carrier (Homsetoid a b)

  _≈_ : {a b : Obj} → Rel (Hom a b) ℓ
  _≈_ {a} {b} = equaloid (Homsetoid a b)

  field
    _∘_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    id : {a : Obj} → Hom a a

-- axioms
  field
    id-r : ∀ {a b} {f : Hom a b} → f ∘ id ≈ f
    id-l : ∀ {a b} {f : Hom a b} → id ∘ f ≈ f
    ∘-assoc : ∀ {a b c d} {f : Hom c d} {g : Hom  b c} {h : Hom a b} → f ∘ g ∘ h ≈ (f ∘ g) ∘ h
    ∘-resp-≈ : ∀ {a b c} {f g : Hom b c} {h i : Hom a b} →
               f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i

open Category hiding (_≈_ ; _∘_ ) public

infix 4 _[_≈_]
infixr 9 _[_∘_]

_[_≈_] : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b : Obj C} → Rel (Hom C a b) ℓ
_[_≈_] C {a} {b} = equaloid (Homsetoid C a b)

_[_∘_] : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = Category._∘_ C f g

≈-isEquiv : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b : Obj C} → IsEquivalence (_[_≈_] C {a} {b})
≈-isEquiv C {a} {b} = isEquivalence (Homsetoid C a b)

≈-refl : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b : Obj C} {f : Hom C a b} → C [ f ≈ f ]
≈-refl C = IsEquivalence.refl (≈-isEquiv C)

≈-sym : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b : Obj C} {f g : Hom C a b} → C [ f ≈ g ] → C [ g ≈ f ]
≈-sym C = IsEquivalence.sym (≈-isEquiv C)

≈-trans : {c₀ c₁ ℓ : Level} (C : Category c₀ c₁ ℓ) {a b : Obj C} {f g h : Hom C a b} → C [ f ≈ g ] → C [ g ≈ h ] → C [ f ≈ h ]
≈-trans C = IsEquivalence.trans (≈-isEquiv C)

op : {c₀ c₁ ℓ : Level} → Category c₀ c₁ ℓ → Category c₀ c₁ ℓ
op C = record {
      Obj = Obj C ;
      Homsetoid = flip (Homsetoid C) ;
      _∘_ = flip (_[_∘_] C) ;
      id = id C ;
      id-r = id-l C ;
      id-l = id-r C ;
      ∘-assoc = ≈-sym C (∘-assoc C) ;
      ∘-resp-≈ = flip (∘-resp-≈ C) }
