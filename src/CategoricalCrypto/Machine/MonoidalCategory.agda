{-# OPTIONS --safe #-}

-- ============================================================================
-- The machine category is a symmetric monoidal category, with hom equality
-- the bisimulation `_≅ᴹ_`.  This module only assembles the records; every law
-- is proved elsewhere:
--
--   bifunctoriality of `_⊗₁_`   `⊗₁-resp-≅ᴹ` (Iso), `⊗₁-id` (Forwarder),
--                               `⊗₁-interchange` (Monoidal.Interchange);
--   iso laws, triangle, pentagon, hexagon, σ∘σ
--                               `Monoidal.Coherence`;
--   naturality of `⊗-assoc⃖`    `Monoidal.Associator`;
--   naturality of the unitors   `Monoidal.Unitors`;
--   naturality of `⊗-symₘ`      `Monoidal.Braiding`.
--
-- The four remaining naturality squares (the forward associator and the
-- inverse unitors) are conjugates of the proved ones.
--
-- Everything downstream that only needs "a symmetric monoidal category of
-- machines" should go through the bundles at the bottom; in particular
-- `CategoricalCrypto.Standard2.StdUC machine-monoidal-category ℰ` instantiates
-- the abstract UC layer at concrete machines.  The names follow
-- `CategoricalCrypto.Channel.Category`.
-- ============================================================================

module CategoricalCrypto.Machine.MonoidalCategory where

open import categorical-crypto.Prelude hiding (id; _∘_; Bifunctor)

open import Categories.Category using (Category)
open import Categories.Category.Product using (Product)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Forwarder using (⊗₁-id)
open import CategoricalCrypto.Machine.Monoidal.Interchange using (⊗₁-interchange)
open import CategoricalCrypto.Machine.Monoidal.Associator using (⊗-assoc⃖-natural)
open import CategoricalCrypto.Machine.Monoidal.Coherence
open import CategoricalCrypto.Machine.Monoidal.Unitors using (λ⇒-natural; ρ⇒-natural)
open import CategoricalCrypto.Machine.Monoidal.Braiding using (σ-natural)

open Mor MachineCategory using (_≅_)
open MR MachineCategory using (conjugate-from; conjugate-to)

-- ----------------------------------------------------------------------------
-- The tensor, as a bifunctor.
-- ----------------------------------------------------------------------------

machine-⊗-bifunctor : Bifunctor MachineCategory MachineCategory MachineCategory
machine-⊗-bifunctor = record
  { F₀           = λ (A , B) → A ⊗₀ B
  ; F₁           = λ (f , g) → f ⊗₁ g
  ; identity     = ⊗₁-id
  ; homomorphism = λ { {f = f , h} {g , k} → ⊗₁-interchange f g h k }
  ; F-resp-≈     = λ (φ , ψ) → ⊗₁-resp-≅ᴹ φ ψ
  }

-- ----------------------------------------------------------------------------
-- The structural isomorphisms.
-- ----------------------------------------------------------------------------

unitorˡ-iso : ∀ {A} → (I ⊗₀ A) ≅ A
unitorˡ-iso = record { from = λ⇒ ; to = λ⇐ ; iso = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ } }

unitorʳ-iso : ∀ {A} → (A ⊗₀ I) ≅ A
unitorʳ-iso = record { from = ρ⇒ ; to = ρ⇐ ; iso = record { isoˡ = ρ-isoˡ ; isoʳ = ρ-isoʳ } }

associator-iso : ∀ {A B C} → ((A ⊗₀ B) ⊗₀ C) ≅ (A ⊗₀ (B ⊗₀ C))
associator-iso = record
  { from = ⊗-assoc ; to = ⊗-assoc⃖ ; iso = record { isoˡ = α-isoˡ ; isoʳ = α-isoʳ } }

-- ----------------------------------------------------------------------------
-- The records.
-- ----------------------------------------------------------------------------

machine-monoidal : Monoidal MachineCategory
machine-monoidal = record
  { ⊗                    = machine-⊗-bifunctor
  ; unit                 = I
  ; unitorˡ              = unitorˡ-iso
  ; unitorʳ              = unitorʳ-iso
  ; associator           = associator-iso
  ; unitorˡ-commute-from = λ {_} {_} {f} → λ⇒-natural f
  ; unitorˡ-commute-to   = λ {_} {_} {f} →
      conjugate-from unitorˡ-iso unitorˡ-iso (≅ᴹ-sym (λ⇒-natural f))
  ; unitorʳ-commute-from = λ {_} {_} {f} → ρ⇒-natural f
  ; unitorʳ-commute-to   = λ {_} {_} {f} →
      conjugate-from unitorʳ-iso unitorʳ-iso (≅ᴹ-sym (ρ⇒-natural f))
  ; assoc-commute-from   = λ {_} {_} {f} {_} {_} {g} {_} {_} {h} →
      ≅ᴹ-sym (conjugate-to associator-iso associator-iso (≅ᴹ-sym (⊗-assoc⃖-natural f g h)))
  ; assoc-commute-to     = λ {_} {_} {f} {_} {_} {g} {_} {_} {h} →
      ≅ᴹ-sym (⊗-assoc⃖-natural f g h)
  ; triangle             = triangle
  ; pentagon             = pentagon
  }

machine-symmetric : Symmetric machine-monoidal
machine-symmetric = symmetricHelper machine-monoidal record
  { braiding    = niHelper record
      { η       = λ (A , B) → ⊗-symₘ {A} {B}
      ; η⁻¹     = λ (A , B) → ⊗-symₘ {B} {A}
      ; commute = λ (f , g) → σ-natural f g
      ; iso     = λ _ → record { isoˡ = σ-σ ; isoʳ = σ-σ }
      }
  ; commutative = σ-σ
  ; hexagon     = hexagon
  }

-- ----------------------------------------------------------------------------
-- The bundles.
-- ----------------------------------------------------------------------------

machine-symmetric-monoidal-category : SymmetricMonoidalCategory _ _ _
machine-symmetric-monoidal-category = record
  { U = MachineCategory ; monoidal = machine-monoidal ; symmetric = machine-symmetric }

machine-monoidal-category : MonoidalCategory _ _ _
machine-monoidal-category = SymmetricMonoidalCategory.monoidalCategory machine-symmetric-monoidal-category
