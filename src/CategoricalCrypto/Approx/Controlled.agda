{-# OPTIONS --safe --without-K #-}

-- Controlled maps: the resource-aware morphisms of approximate spaces
-- (`docs/quantitative-uc-setup-plan.typ` §7.2).
--
-- A nonexpansive map keeps its bound; a resource-sensitive pullback TRANSFORMS
-- it, and the transformation is part of the morphism rather than a side
-- condition on it.  `Control` is what such a transformation must be — a lax
-- ordered additive endomorphism of the errors — and `Controlled` is a function
-- carrying one.
--
-- Everything is stated with `⊑`, in the direction that makes a BOUND
-- admissible: the intended model's own allowance arithmetic is exact when a
-- morphism is absorbed into a test and only an inequality when it is absorbed
-- into a closure (`UC.Budget.ctxBudget-simCost` against
-- `ctxBudget-closure≤`), so demanding equations here would exclude the model
-- this category exists to hold.
--
-- Hom equality compares the controls pointwise and the functions at zero error.
-- Composition respects it because a control preserves zero — that is the one
-- place `preserves-ε₀` is spent, and it is also why `Ctrl` forgets to `Setoids`
-- at all.  Controls are never erased from the categorical data.

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import Data.Product.Base using (_×_; _,_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Controlled
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E

private variable c ℓa : Level

------------------------------------------------------------------------
-- The error transformations a morphism may carry

record Control : Set (es ⊔ ℓe) where
  field
    at           : Error → Error
    preserves-ε₀ : at ε₀ ⊑ ε₀
    preserves-⊕  : {ε δ : Error} → at (ε ⊕ δ) ⊑ at ε ⊕ at δ
    monotone     : {ε δ : Error} → ε ⊑ δ → at ε ⊑ at δ

open Control using (at)

idᶜ : Control
idᶜ = record
  { at = λ ε → ε ; preserves-ε₀ = ⊑-refl ; preserves-⊕ = ⊑-refl ; monotone = λ le → le }

infixr 9 _∘ᶜ_

_∘ᶜ_ : Control → Control → Control
ψ ∘ᶜ φ = record
  { at           = λ ε → ψ.at (φ.at ε)
  ; preserves-ε₀ = ⊑-trans (ψ.monotone φ.preserves-ε₀) ψ.preserves-ε₀
  ; preserves-⊕  = ⊑-trans (ψ.monotone φ.preserves-⊕) ψ.preserves-⊕
  ; monotone     = λ le → ψ.monotone (φ.monotone le)
  }
  where module ψ = Control ψ
        module φ = Control φ

------------------------------------------------------------------------
-- …and the morphisms carrying them

record Controlled (X Y : ApproxSpace c ℓa) : Set (c ⊔ es ⊔ ℓe ⊔ ℓa) where
  private
    module X = ApproxSpace X
    module Y = ApproxSpace Y

  field
    map       : X.Carrier → Y.Carrier
    control   : Control
    preserves : {x y : X.Carrier} {ε : Error}
              → x X.≈[ ε ] y → map x Y.≈[ at control ε ] map y

module _ {X Y : ApproxSpace c ℓa} where
  private module Y = ApproxSpace Y

  open Controlled

  infix 4 _≈ᶜ_

  _≈ᶜ_ : Controlled X Y → Controlled X Y → Set (c ⊔ es ⊔ ℓa)
  f ≈ᶜ g = ((ε : Error) → at (control f) ε ≡ at (control g) ε)
         × ((x : ApproxSpace.Carrier X) → map f x Y.≈[ ε₀ ] map g x)

  ≈ᶜ-isEquivalence : IsEquivalence _≈ᶜ_
  ≈ᶜ-isEquivalence = record
    { refl  = (λ _ → refl) , λ _ → Y.≈[]-refl
    ; sym   = λ (ce , me) → (λ ε → sym (ce ε)) , λ x → Y.≈[]-sym (me x)
    ; trans = λ (ce₁ , me₁) (ce₂ , me₂) →
        (λ ε → trans (ce₁ ε) (ce₂ ε))
        , λ x → Y.≈[]-mono ⊕-identityˡ (Y.≈[]-trans (me₁ x) (me₂ x))
    }

identityᶜ : {X : ApproxSpace c ℓa} → Controlled X X
identityᶜ = record { map = λ x → x ; control = idᶜ ; preserves = λ h → h }

composeᶜ : {X Y Z : ApproxSpace c ℓa} → Controlled Y Z → Controlled X Y → Controlled X Z
composeᶜ g f = record
  { map       = λ x → map g (map f x)
  ; control   = control g ∘ᶜ control f
  ; preserves = λ h → preserves g (preserves f h)
  }
  where open Controlled

-- The zero-error half is where a control's preservation of zero is spent: the
-- outer leg is applied to an ε₀-comparison and must give one back.
composeᶜ-resp : {X Y Z : ApproxSpace c ℓa}
                {g g′ : Controlled Y Z} {f f′ : Controlled X Y}
              → g ≈ᶜ g′ → f ≈ᶜ f′ → composeᶜ g f ≈ᶜ composeᶜ g′ f′
composeᶜ-resp {Z = Z} {g = g} {f′ = f′} (ce₁ , me₁) (ce₂ , me₂) =
  (λ ε → trans (cong (at (Controlled.control g)) (ce₂ ε)) (ce₁ (at (Controlled.control f′) ε)))
  , λ x → Z.≈[]-mono ⊕-identityˡ (Z.≈[]-trans
      (Z.≈[]-mono (Control.preserves-ε₀ (Controlled.control g))
                  (Controlled.preserves g (me₂ x)))
      (me₁ (Controlled.map f′ x)))
  where module Z = ApproxSpace Z

Ctrl : (c ℓa : Level) → Category (suc (c ⊔ ℓa) ⊔ es ⊔ ℓe) (c ⊔ es ⊔ ℓe ⊔ ℓa) (c ⊔ es ⊔ ℓa)
Ctrl c ℓa = record
  { Obj       = ApproxSpace c ℓa
  ; _⇒_       = Controlled
  ; _≈_       = _≈ᶜ_
  ; id        = identityᶜ
  ; _∘_       = composeᶜ
  ; assoc     = λ {_} {_} {_} {D} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl D
  ; sym-assoc = λ {_} {_} {_} {D} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl D
  ; identityˡ = λ {_} {B} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl B
  ; identityʳ = λ {_} {B} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl B
  ; identity² = λ {A} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl A
  ; equiv     = λ {A} {B} → ≈ᶜ-isEquivalence {X = A} {Y = B}
  ; ∘-resp-≈  = λ {A} {B} {C} {f} {h} {g} {i} →
      composeᶜ-resp {X = A} {Y = B} {Z = C} {g = f} {g′ = h} {f = g} {f′ = i}
  }

------------------------------------------------------------------------
-- The nonexpansive theory sits inside

controlled : {X Y : ApproxSpace c ℓa} → Nonexpansive X Y → Controlled X Y
controlled f = record
  { map = Nonexpansive.map f ; control = idᶜ ; preserves = Nonexpansive.preserves f }

include : Functor (Approx c ℓa) (Ctrl c ℓa)
include = record
  { F₀ = λ X → X
  ; F₁ = controlled
  ; identity     = λ {A} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl A
  ; homomorphism = λ {_} {_} {Z} → (λ _ → refl) , λ _ → ApproxSpace.≈[]-refl Z
  ; F-resp-≈     = λ {_} {B} e → (λ _ → refl) , e
  }
