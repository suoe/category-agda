import Category

module Morphism {c₀ c₁ ℓ} (C : Category.Category c₀ c₁ ℓ) where

open Category.Category C
open import Level
import Relation.Binary.EqReasoning as EqReasoning

record Isomorphism {a b : Obj} (f : Hom a b) : Set (c₀ ⊔ c₁ ⊔ ℓ) where
  field
    inverse : Hom b a
    proof₁ : f ∘ inverse ≈ id
    proof₂ : inverse ∘ f ≈ id

record _≅_ (a b : Obj) : Set (c₀ ⊔ c₁ ⊔ ℓ) where
  field
    iso : Hom a b
    proof : Isomorphism iso


record Monomorphism {a b : Obj} (f : Hom a b) : Set (c₀ ⊔ c₁ ⊔ ℓ) where
  field
    elim-l : ∀ {c : Obj} {g g′ : Hom c a} → f ∘ g ≈ f ∘ g′ → g ≈ g′

record Epimorphism {a b : Obj} (f : Hom a b) : Set (c₀ ⊔ c₁ ⊔ ℓ) where
  field
    elim-r : ∀ {c : Obj} {g g′ : Hom b c} → g ∘ f ≈ g′ ∘ f → g ≈ g′
