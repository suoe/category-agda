module Mappoid where

open import Level
open import Relation.Binary
open Setoid renaming (_≈_ to equaloid)

record Mappoid {a b ℓ ℓ′} (A : Setoid a ℓ) (B : Setoid b ℓ′) : Set (a ⊔ b ⊔ ℓ ⊔ ℓ′) where
  field
    map : Carrier A → Carrier B
    resp-equaloid : ∀ {x y} → equaloid A x y → equaloid B (map x) (map y)

