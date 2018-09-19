module Functor where

open import Level
open import Relation.Binary
open Setoid renaming (_≈_ to equaloid)
open import Category
open import Mappoid

record Functor {c₀ c₁ ℓ c₀′ c₁′ ℓ′ : Level} (C : Category c₀ c₁ ℓ) (D : Category c₀′ c₁′ ℓ′) : Set (suc (c₀ ⊔ c₁ ⊔ ℓ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ′)) where
  field
    fobj : Obj C → Obj D
    fmappoid : {a b : Obj C} → Mappoid (Homsetoid C a b) (Homsetoid D (fobj a) (fobj b))

  fmap : {a b : Obj C} → Hom C a b → Hom D (fobj a) (fobj b)
  fmap f = Mappoid.map fmappoid f

  field
    resp-id : ∀ {a} → D [ fmap (id C {a}) ≈ id D {fobj a} ]
    distrib : ∀ {a b c} {f : Hom C b c} {g : Hom C a b} → D [ fmap (C [ f ∘ g ]) ≈ D [ fmap f ∘ fmap g ] ]

  resp-≈ : {a b : Obj C} {f g : Hom C a b} → C [ f ≈ g ] → D [ fmap f ≈ fmap g ]
  resp-≈ f≈g = Mappoid.resp-equaloid fmappoid f≈g

  resp-~ : {a b c d : Obj C} {f : Hom C a b} {g : Hom C c d} → C [ f ~ g ] → D [ fmap f ~ fmap g ]
  resp-~ (≈-~ f≈g) = ≈-~ (resp-≈ f≈g)



open Functor public

_≈F_ : {c₀ c₁ ℓ c₀′ c₁′ ℓ′ : Level} {C : Category c₀ c₁ ℓ} {D : Category c₀′ c₁′ ℓ′} → Rel (Functor C D) (c₀ ⊔ (c₁ ⊔ (suc c₀′ ⊔ (suc c₁′ ⊔ suc ℓ′))))
_≈F_ {C = C} {D} F G = ∀ {a b : Obj C} (f : Hom C a b) → D [ fmap F f ~ fmap G f ]

_∘F_ : {c₀ c₁ ℓ d₀ d₁ ℓ′ e₀ e₁ ℓ′′ : Level} {C : Category c₀ c₁ ℓ} {D : Category d₀ d₁ ℓ′} {E : Category e₀ e₁ ℓ′′} → Functor D E → Functor C D → Functor C E
_∘F_ {E = E} F G = record {
  fobj = λ x → fobj F (fobj G x) ;
  fmappoid = fmappoid F ∘M fmappoid G ;
  resp-id = λ {a} → ≈-trans E (resp-≈ F (resp-id G {a})) (resp-id F {fobj G a}) ;
  distrib = λ {a} {b} {c} {f} {g} →  ≈-trans E (resp-≈ F (distrib G {f = f} {g})) (distrib F {f = fmap G f} {fmap G g})
  }

idF : {c₀ c₁ ℓ : Level} {C : Category c₀ c₁ ℓ} → Functor C C
idF {C = C} = record {
  fobj = λ x → x ;
  fmappoid = idM ;
  resp-id = ≈-refl C ;
  distrib = ≈-refl C
  }

Cat : ∀ {c₀ c₁ ℓ} → Category (suc (c₀ ⊔ c₁ ⊔ ℓ)) (suc (c₀ ⊔ c₁ ⊔ ℓ)) (suc (c₀ ⊔ c₁ ⊔ ℓ))
Cat {c₀} {c₁} {ℓ} = record {
  Obj = Category c₀ c₁ ℓ ;
  Homsetoid = λ C D → record {
    Carrier = Functor C D ;
    _≈_ = _≈F_;
    isEquivalence = record {
      refl = λ {F} → λ f → ~-refl D ;
      sym = λ F≈G → λ f → ~-sym D (F≈G f) ;
      trans = λ F≈G G≈H → λ f → ~-trans D (F≈G f) (G≈H f)
      }
    } ;
  _∘_ = _∘F_ ;
  id = idF ;
  id-r = λ {C} {D} → λ f → ~-refl D ;
  id-l = λ {C} {D} → λ f → ~-refl D ;
  ∘-assoc = λ {A} {B} {C} {D} {F} {G} {H} → λ f → ~-refl D ;
  ∘-resp-≈ = λ {A} {B} {C} {F} {G} {H} {I} F≈G H≈I → λ f → ~-trans C (resp-~ F (H≈I f)) (F≈G (fmap I f))
  }
