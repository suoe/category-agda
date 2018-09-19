module Nat where

open import Level
open import Category
open import Functor

record Nat {c₀ c₁ ℓ c₀′ c₁′ ℓ′} {C : Category c₀ c₁ ℓ} {D : Category c₀′ c₁′ ℓ′} (F G : Functor C D)
                                     : Set (suc (c₀ ⊔ c₁ ⊔ ℓ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ′)) where
  field
    component : (a : Obj C) → Hom D (fobj F a) (fobj G a)
    naturality : ∀ {a b} {f : Hom C a b} → D [ D [ fmap G f ∘ component a ] ≈ D [ component b ∘ fmap F f ] ]
