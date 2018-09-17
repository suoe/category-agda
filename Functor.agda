module Functor where

open import Level
open import Relation.Binary
open Setoid renaming (_≈_ to equaloid)
open import Category
open import Mappoid

record Functor {c₀ c₁ ℓ c₀′ c₁′ ℓ′ : Level} (C : Category c₀ c₁ ℓ) (D : Category c₀′ c₁′ ℓ): Set (suc (c₀ ⊔ c₁ ⊔ ℓ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ′)) where
  field
    fobj : Obj C → Obj D
    fmappoid : {a b : Obj C} → Mappoid (Homsetoid C a b) (Homsetoid D (fobj a) (fobj b))

  fmap : {a b : Obj C} → Hom C a b → Hom D (fobj a) (fobj b)
  fmap f = Mappoid.map fmappoid f

  field
    resp-id : ∀ {a} → D [ fmap (id C {a}) ≈ id D {fobj a} ]
    distrib : ∀ {a b c} {f : Hom C b c} {g : Hom C a b} → D [ fmap (C [ f ∘ g ]) ≈ D [ fmap f ∘ fmap g ] ]
