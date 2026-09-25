{-# OPTIONS --safe --without-K #-}

-- Graded wide subcategories of a monoidal category C, cut out by a grade-indexed
-- certificate predicate.

module Categories.LocallyGraded.SubCategory where

open import Data.Product
open import Data.Unit.Polymorphic
open import Level

open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Monoidal
open import Categories.LocallyGraded.Trivial

module _ {oi ℓi ei o ℓ e p} {ℐ : MonoidalCategory oi ℓi ei} {C : MonoidalCategory o ℓ e} where
  private module ℐ = MonoidalCategory ℐ; module C = MonoidalCategory C
  record Predicate (P : ℐ.Obj → ∀ {A B} → A C.⇒ B → Set p)
                   (X : ℐ.Obj) (A B : C.Obj) : Set (ℓ ⊔ p) where
    constructor _,_
    field arr  : A C.⇒ B
          Parr : P X arr

record GradedSubCat {oi ℓi ei o ℓ e} (ℐ : MonoidalCategory oi ℓi ei)
    (C : MonoidalCategory o ℓ e) (p : Level) : Set (oi ⊔ ℓi ⊔ o ⊔ ℓ ⊔ e ⊔ suc p) where
  private module ℐ = MonoidalCategory ℐ
  open MonoidalCategory C

  field
    Pred : ℐ.Obj → ∀ {A B} → A ⇒ B → Set p
    pred-resp : ∀ {X A B} {f g : A ⇒ B} → f ≈ g → Pred X f → Pred X g
    pred-sub : ∀ {X Y A B} {f : A ⇒ B} → X ℐ.⇒ Y → Pred X f → Pred Y f
    pred-id : ∀ {A} → Pred ℐ.unit (id {A})
    pred-∘ : ∀ {X Y A B D} {g : B ⇒ D} {f : A ⇒ B} → Pred Y g → Pred X f → Pred (X ℐ.⊗₀ Y) (g ∘ f)
    pred-⊗ : ∀ {X Y A B A′ B′} {f : A ⇒ B} {g : A′ ⇒ B′}
           → Pred X f → Pred Y g → Pred (X ℐ.⊗₀ Y) (f ⊗₁ g)
    pred-α⇒ : ∀ {A B D} → Pred ℐ.unit (associator.from {A} {B} {D})
    pred-α⇐ : ∀ {A B D} → Pred ℐ.unit (associator.to {A} {B} {D})
    pred-λ⇒ : ∀ {A} → Pred ℐ.unit (unitorˡ.from {A})
    pred-λ⇐ : ∀ {A} → Pred ℐ.unit (unitorˡ.to {A})
    pred-ρ⇒ : ∀ {A} → Pred ℐ.unit (unitorʳ.from {A})
    pred-ρ⇐ : ∀ {A} → Pred ℐ.unit (unitorʳ.to {A})

  L : LocallyGradedCategory ℐ o (ℓ ⊔ p) e
  L = record
    { Obj              = Obj
    ; Hom              = Predicate {ℐ = ℐ} {C} Pred
    ; _≈_              = λ h h′ → Predicate.arr h ≈ Predicate.arr h′
    ; equiv            = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
    ; sub[_]           = λ a (f , cf) → f , pred-sub a cf
    ; sub-identity     = Equiv.refl
    ; sub-homomorphism = Equiv.refl
    ; sub-resp-≈       = λ _ f≈g → f≈g
    ; id               = id , pred-id
    ; _∙_              = λ (g , cg) (f , cf) → g ∘ f , pred-∘ cg cf
    ; ∙-resp-≈         = ∘-resp-≈
    ; identityˡ        = identityˡ
    ; identityʳ        = identityʳ
    ; assoc            = assoc
    ; interchange      = Equiv.refl
    }

  private module L = LocallyGradedCategory L

  ⌊_⌋ : ∀ {X A B} → L.Hom X A B → A ⇒ B
  ⌊_⌋ = Predicate.arr

  U-faithful : ∀ {X A B} {h h′ : L.Hom X A B} → ⌊ h ⌋ ≈ ⌊ h′ ⌋ → h L.≈ h′
  U-faithful h≈h′ = h≈h′

  forget : LocallyGradedFunctor L (Trivial ℐ U)
  forget = record
    { F₀ = λ A → A ; F₁ = ⌊_⌋ ; F-resp-≈ = λ h≈h′ → h≈h′
    ; F-sub = Equiv.refl ; identity = Equiv.refl ; homomorphism = Equiv.refl }

  module _ (Braided-ℐ : Braided ℐ.monoidal) where

    monoidalᴸ : GradedMonoidal Braided-ℐ L
    monoidalᴸ = record
      { _⊗₀_            = _⊗₀_
      ; unit            = unit
      ; _⊗₁_            = λ (f , cf) (g , cg) → f ⊗₁ g , pred-⊗ cf cg
      ; ⊗-resp-≈        = λ f≈f′ g≈g′ → ⊗.F-resp-≈ (f≈f′ , g≈g′)
      ; ⊗-sub           = Equiv.refl
      ; ⊗-identity      = ⊗.identity
      ; ⊗-homomorphism  = Equiv.sym ⊗.homomorphism
      ; associator      = record
        { from = _ , pred-α⇒ ; to = _ , pred-α⇐ ; isoˡ = associator.isoˡ ; isoʳ = associator.isoʳ }
      ; unitorˡ         = record
        { from = _ , pred-λ⇒ ; to = _ , pred-λ⇐ ; isoˡ = unitorˡ.isoˡ ; isoʳ = unitorˡ.isoʳ }
      ; unitorʳ         = record
        { from = _ , pred-ρ⇒ ; to = _ , pred-ρ⇐ ; isoˡ = unitorʳ.isoˡ ; isoʳ = unitorʳ.isoʳ }
      ; assoc-commute   = assoc-commute-from
      ; unitorˡ-commute = unitorˡ-commute-from
      ; unitorʳ-commute = unitorʳ-commute-from
      ; triangle        = triangle
      ; pentagon        = pentagon
      }

    GradedMonoidal-forget : GradedMonoidalFunctor monoidalᴸ (Trivial-monoidal Braided-ℐ C) forget
    GradedMonoidal-forget = record
      { ε              = id
      ; ⊗-homo         = id
      ; ⊗-homo-commute = Equiv.trans identityˡ (Equiv.sym identityʳ)
      ; associativity  = Equiv.trans id-cancel (Equiv.sym id-cancelˡ)
      ; unitaryˡ       = id-cancel
      ; unitaryʳ       = id-cancel
      }
      where
      id-cancel : ∀ {A B D} {f : A ⊗₀ B ⇒ D} → f ∘ id ∘ id {A} ⊗₁ id {B} ≈ f
      id-cancel = Equiv.trans (∘-resp-≈ʳ (Equiv.trans identityˡ ⊗.identity)) identityʳ
      id-cancelˡ : ∀ {A D E} {f : A ⇒ D ⊗₀ E} → id ∘ id {D} ⊗₁ id {E} ∘ f ≈ f
      id-cancelˡ = Equiv.trans identityˡ (Equiv.trans (∘-resp-≈ˡ ⊗.identity) identityˡ)

-- the entire category
unrestricted : ∀ {oi ℓi ei o ℓ e p} (ℐ : MonoidalCategory oi ℓi ei) (C : MonoidalCategory o ℓ e)
             → GradedSubCat ℐ C p
unrestricted ℐ C = record
  { Pred = λ _ _ → ⊤ ; pred-resp = λ _ _ → tt ; pred-sub = λ _ _ → tt ; pred-id = tt
  ; pred-∘ = λ _ _ → tt ; pred-⊗ = λ _ _ → tt ; pred-α⇒ = tt ; pred-α⇐ = tt
  ; pred-λ⇒ = tt ; pred-λ⇐ = tt ; pred-ρ⇒ = tt ; pred-ρ⇐ = tt }
