{-# OPTIONS --safe --without-K #-}

-- Controlled maps: the resource-aware morphisms of approximate spaces.
--
-- A nonexpansive map keeps its bound; a resource-sensitive pullback TRANSFORMS
-- it, and the transformation is part of the morphism rather than a side
-- condition on it.
--
-- A `Control` is a monotone map of the error preorder (stdlib's
-- `PreorderHomomorphism`) that does not raise zero and is subadditive.  Read
-- `⊑` as arrows, those two laws point the OPLAX way (`φ ε₀ → ε₀`,
-- `φ (ε ⊕ δ) → φ ε ⊕ φ δ`), but the errors are only a lax-unital preordered
-- magma, so no oplax monoidal functor is claimed.
--
-- Everything is stated with `⊑`, in the direction that makes a BOUND
-- admissible: the intended model's allowance substitutions are equations
-- (`Data.Nat.Positive.scale-·`, `scale-comm`), but a model whose resource
-- certificates only bound an allowance from above reads them through an
-- inequality, and demanding equations here would exclude it.
--
-- Two controls are compared in the ERRORS' OWN ORDER (`_≐ᶜ_`), not by
-- propositional equality: at a schedule-valued error `at φ ε` is itself a
-- function, and agreement of two such is not an equation without funext.

open import Data.Product.Base using (_×_; _,_)
open import Level
open import Relation.Binary.Morphism.Bundles
open import Relation.Binary.PropositionalEquality

import Relation.Binary.Morphism.Construct.Composition as Comp
import Relation.Binary.Morphism.Construct.Identity as Id

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Controlled
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E

private variable c ℓa : Level

------------------------------------------------------------------------
-- The error transformations a morphism may carry

record Control : Set (es ⊔ ℓe) where
  field homomorphism : PreorderHomomorphism ⊑-preorder ⊑-preorder

  open PreorderHomomorphism homomorphism public renaming (⟦_⟧ to at)

  field
    preserves-ε₀ : at ε₀ ⊑ ε₀
    preserves-⊕  : {ε δ : Error} → at (ε ⊕ δ) ⊑ at ε ⊕ at δ

open Control

idᶜ : Control
idᶜ = record
  { homomorphism = Id.preorderHomomorphism ⊑-preorder ; preserves-ε₀ = ⊑-refl ; preserves-⊕ = ⊑-refl }

infixr 9 _∘ᶜ_

_∘ᶜ_ : Control → Control → Control
ψ ∘ᶜ φ = record
  { homomorphism = Comp.preorderHomomorphism φ.homomorphism ψ.homomorphism
  ; preserves-ε₀ = ⊑-trans (ψ.mono φ.preserves-ε₀) ψ.preserves-ε₀
  ; preserves-⊕  = ⊑-trans (ψ.mono φ.preserves-⊕) ψ.preserves-⊕
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

infix 4 _≐_ _≐ᶜ_

_≐_ : (Error → Error) → (Error → Error) → Set (es ⊔ ℓe)
f ≐ g = ((ε : Error) → f ε ⊑ g ε) × ((ε : Error) → g ε ⊑ f ε)

_≐ᶜ_ : Control → Control → Set (es ⊔ ℓe)
φ ≐ᶜ ψ = at φ ≐ at ψ

-- Every law below is this at `refl`, stated on the transformations because
-- the controls it compares agree only under `at` (a composite's own law fields
-- are built with `⊑-trans`), which leaves `{φ : Control} → φ ≐ᶜ φ` unusable.
≐-reflexive : {f g : Error → Error} → f ≡ g → f ≐ g
≐-reflexive refl = (λ _ → ⊑-refl) , λ _ → ⊑-refl

module _ {X Y : ApproxSpace c ℓa} where
  private module Y = ApproxSpace Y

  open Controlled

  infix 4 _≈ᶜ_

  _≈ᶜ_ : Controlled X Y → Controlled X Y → Set (c ⊔ es ⊔ ℓe ⊔ ℓa)
  f ≈ᶜ g = (control f ≐ᶜ control g)
         × ((x : ApproxSpace.Carrier X) → map f x Y.≈[ ε₀ ] map g x)

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
composeᶜ-resp {Z = Z} {g = g} {f′ = f′} ((l₁ , r₁) , me₁) ((l₂ , r₂) , me₂) =
  ( (λ ε → ⊑-trans (Control.mono ψ (l₂ ε)) (l₁ (at φ′ ε)))
  , (λ ε → ⊑-trans (r₁ (at φ′ ε)) (Control.mono ψ (r₂ ε))) )
  , λ x → Z.≈[]-trans₀ (Z.≈[]-mono (Control.preserves-ε₀ ψ) (Controlled.preserves g (me₂ x)))
                       (me₁ (Controlled.map f′ x))
  where module Z = ApproxSpace Z
        ψ  = Controlled.control g
        φ′ = Controlled.control f′
