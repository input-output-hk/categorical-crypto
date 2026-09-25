{-# OPTIONS --safe --without-K #-}

-- Resource-admissible families of graded processes: objects are `Ix`-indexed
-- families of objects of C, and a hom is a levelwise graded hom of a graded
-- wide subcategory whose grade follows a schedule `ℕ → ℐ.Obj` read at `κ i`,
-- the schedule drawn from an admissible class closed under the unit and ⊗.
--
-- Equality compares the INTERPRETATIONS levelwise and forgets schedules and
-- certificates, so two homs whose upper-bound annotations differ can still be
-- equal. That is what makes the family category monoidal with every law read
-- off C, and what separates it from an exact-grade category whose equality
-- keeps the grade (`CategoricalCrypto.UC.Quantitative.Query.𝒞ᵇ`).

module Categories.LocallyGraded.Family where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (monoidalHelper)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

module Families {oi ℓi ei o ℓ e p a}
  {ℐ : MonoidalCategory oi ℓi ei} {C : MonoidalCategory o ℓ e}
  (G : GradedSubCat ℐ C p) (Ix : Set) (κ : Ix → ℕ)
  (Admissible : (ℕ → MonoidalCategory.Obj ℐ) → Set a)
  (adm-unit : Admissible (λ _ → MonoidalCategory.unit ℐ))
  (adm-⊗ : ∀ {s t} → Admissible s → Admissible t
         → Admissible (λ n → MonoidalCategory._⊗₀_ ℐ (s n) (t n))) where

  private module ℐ = MonoidalCategory ℐ
  open MonoidalCategory C
  open GradedSubCat G
  private module L = LocallyGradedCategory L

  Obj^ω : Set o
  Obj^ω = Ix → Obj

  Δ : Obj → Obj^ω
  Δ X _ = X

  infixr 8 _⊛ω_

  _⊛ω_ : Obj^ω → Obj^ω → Obj^ω
  (A ⊛ω B) i = A i ⊗₀ B i

  private variable A B D E : Obj^ω

  infix 10 _⇒^ω_
  infix 4 _≈^ω_

  _⇒^ω_ : Obj^ω → Obj^ω → Set (oi ⊔ a ⊔ ℓ ⊔ p)
  A ⇒^ω B = Σ[ s ∈ (ℕ → ℐ.Obj) ] Admissible s × ((i : Ix) → L.Hom (s (κ i)) (A i) (B i))

  -- The schedule a hom CARRIES, as opposed to one an obligation invents.
  schedOf : A ⇒^ω B → ℕ → ℐ.Obj
  schedOf = proj₁

  schedOf-adm : (f : A ⇒^ω B) → Admissible (schedOf f)
  schedOf-adm f = proj₁ (proj₂ f)

  hom : (f : A ⇒^ω B) (i : Ix) → L.Hom (schedOf f (κ i)) (A i) (B i)
  hom f = proj₂ (proj₂ f)

  _≈^ω_ : (f g : A ⇒^ω B) → Set e
  f ≈^ω g = (i : Ix) → ⌊ hom f i ⌋ ≈ ⌊ hom g i ⌋

  -- the structural homs, at the constant unit schedule
  unit^ω : ((i : Ix) → L.Hom ℐ.unit (A i) (B i)) → A ⇒^ω B
  unit^ω h = (λ _ → ℐ.unit) , adm-unit , h

  Fam : Category o (oi ⊔ a ⊔ ℓ ⊔ p) e
  Fam = record
    { Obj       = Obj^ω
    ; _⇒_       = _⇒^ω_
    ; _≈_       = _≈^ω_
    ; id        = unit^ω λ _ → L.id
    ; _∘_       = λ (t , At , g) (s , As , f) →
        (λ n → s n ℐ.⊗₀ t n) , adm-⊗ As At , λ i → g i L.∙ f i
    ; assoc     = λ _ → assoc
    ; sym-assoc = λ _ → sym-assoc
    ; identityˡ = λ _ → identityˡ
    ; identityʳ = λ _ → identityʳ
    ; identity² = λ _ → identity²
    ; equiv     = record
      { refl = λ _ → Equiv.refl ; sym = λ f≈g i → Equiv.sym (f≈g i)
      ; trans = λ f≈g g≈h i → Equiv.trans (f≈g i) (g≈h i) }
    ; ∘-resp-≈  = λ g≈i f≈h i → ∘-resp-≈ (g≈i i) (f≈h i)
    }

  infixr 10 _⊗^ω_

  _⊗^ω_ : A ⇒^ω B → D ⇒^ω E → (A ⊛ω D) ⇒^ω (B ⊛ω E)
  (s , As , f) ⊗^ω (t , At , g) =
      (λ n → s n ℐ.⊗₀ t n) , adm-⊗ As At
    , λ i → (⌊ f i ⌋ ⊗₁ ⌊ g i ⌋ , pred-⊗ (Parr (f i)) (Parr (g i)))
    where open Predicate

  ⊗^ω-bifunctor : Bifunctor Fam Fam Fam
  ⊗^ω-bifunctor = record
    { F₀           = λ (A , B) → A ⊛ω B
    ; F₁           = λ (f , g) → f ⊗^ω g
    ; identity     = λ _ → ⊗.identity
    ; homomorphism = λ _ → ⊗.homomorphism
    ; F-resp-≈     = λ (ef , eg) i → ⊗.F-resp-≈ (ef i , eg i)
    }

  Famᴹ : MonoidalCategory o (oi ⊔ a ⊔ ℓ ⊔ p) e
  Famᴹ = record
    { U        = Fam
    ; monoidal = monoidalHelper Fam record
      { ⊗          = ⊗^ω-bifunctor
      ; unit       = Δ unit
      ; unitorˡ    = record
        { from = unit^ω λ _ → _ , pred-λ⇒ ; to = unit^ω λ _ → _ , pred-λ⇐
        ; iso  = record { isoˡ = λ _ → unitorˡ.isoˡ ; isoʳ = λ _ → unitorˡ.isoʳ } }
      ; unitorʳ    = record
        { from = unit^ω λ _ → _ , pred-ρ⇒ ; to = unit^ω λ _ → _ , pred-ρ⇐
        ; iso  = record { isoˡ = λ _ → unitorʳ.isoˡ ; isoʳ = λ _ → unitorʳ.isoʳ } }
      ; associator = record
        { from = unit^ω λ _ → _ , pred-α⇒ ; to = unit^ω λ _ → _ , pred-α⇐
        ; iso  = record { isoˡ = λ _ → associator.isoˡ ; isoʳ = λ _ → associator.isoʳ } }
      ; unitorˡ-commute = λ _ → unitorˡ-commute-from
      ; unitorʳ-commute = λ _ → unitorʳ-commute-from
      ; assoc-commute   = λ _ → assoc-commute-from
      ; triangle        = λ _ → triangle
      ; pentagon        = λ _ → pentagon
      }
    }

-- The forgetful interpretation into unrestricted C-families: every certificate
-- and every schedule admitted. Strong, with identity comparison maps.
module _ {oi ℓi ei o ℓ e p a}
  {ℐ : MonoidalCategory oi ℓi ei} {C : MonoidalCategory o ℓ e}
  (G : GradedSubCat ℐ C p) (Ix : Set) (κ : Ix → ℕ)
  (Admissible : (ℕ → MonoidalCategory.Obj ℐ) → Set a)
  (adm-unit : Admissible (λ _ → MonoidalCategory.unit ℐ))
  (adm-⊗ : ∀ {s t} → Admissible s → Admissible t
         → Admissible (λ n → MonoidalCategory._⊗₀_ ℐ (s n) (t n))) where

  private
    module F = Families G Ix κ Admissible adm-unit adm-⊗
    module U = Families (unrestricted {p = 0ℓ} ℐ C) Ix κ (λ _ → ⊤ {0ℓ}) tt (λ _ _ → tt)
  open MonoidalCategory C

  forgetᴹ : StrongMonoidalFunctor F.Famᴹ U.Famᴹ
  forgetᴹ = record
    { F = record
      { F₀ = λ A → A
      ; F₁ = λ f → F.schedOf f , tt , λ i → GradedSubCat.⌊ G ⌋ (F.hom f i) , tt
      ; identity = λ _ → Equiv.refl ; homomorphism = λ _ → Equiv.refl
      ; F-resp-≈ = λ f≈g → f≈g }
    ; isStrongMonoidal = record
      { ε = record { from = U.unit^ω λ _ → id , tt ; to = U.unit^ω λ _ → id , tt
                   ; iso = record { isoˡ = λ _ → identity² ; isoʳ = λ _ → identity² } }
      ; ⊗-homo = niHelper record
        { η = λ _ → U.unit^ω λ _ → id , tt ; η⁻¹ = λ _ → U.unit^ω λ _ → id , tt
        ; commute = λ _ _ → Equiv.trans identityˡ (Equiv.sym identityʳ)
        ; iso = λ _ → record { isoˡ = λ _ → identity² ; isoʳ = λ _ → identity² } }
      ; associativity = λ _ → Equiv.trans id-cancelʳ (Equiv.sym id-cancelˡ)
      ; unitaryˡ = λ _ → id-cancelʳ
      ; unitaryʳ = λ _ → id-cancelʳ
      }
    }
    where
    id-cancelʳ : ∀ {A B D} {f : A ⊗₀ B ⇒ D} → f ∘ id ∘ id {A} ⊗₁ id {B} ≈ f
    id-cancelʳ = Equiv.trans (∘-resp-≈ʳ (Equiv.trans identityˡ ⊗.identity)) identityʳ
    id-cancelˡ : ∀ {A D E} {f : A ⇒ D ⊗₀ E} → id ∘ id {D} ⊗₁ id {E} ∘ f ≈ f
    id-cancelˡ = Equiv.trans identityˡ (Equiv.trans (∘-resp-≈ˡ ⊗.identity) identityˡ)
