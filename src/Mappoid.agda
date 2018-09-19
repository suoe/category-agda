module Mappoid where

open import Level
open import Relation.Binary
open Setoid renaming (_≈_ to equaloid)

record Mappoid {a b ℓ ℓ′} (A : Setoid a ℓ) (B : Setoid b ℓ′) : Set (a ⊔ b ⊔ ℓ ⊔ ℓ′) where
  field
    map : Carrier A → Carrier B
    resp-equaloid : ∀ {x y} → equaloid A x y → equaloid B (map x) (map y)

open Mappoid

_∘M_ : {a b c ℓ ℓ′ ℓ′′ : Level} {A : Setoid a ℓ} {B : Setoid b ℓ′} {C : Setoid c ℓ′′} → Mappoid B C → Mappoid A B → Mappoid A C
f ∘M g = record {
     map = λ x → map f (map g x) ;
     resp-equaloid = λ eq → resp-equaloid f (resp-equaloid g eq)
  }

idM : {a ℓ : Level} {A : Setoid a ℓ} → Mappoid A A
idM = record {
    map = λ x → x ;
    resp-equaloid = λ eq → eq
  }

