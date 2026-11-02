{-# OPTIONS --safe #-}

-- ============================================================================
-- The machine category is a symmetric monoidal category, with hom equality the
-- state isomorphism `_≅ᴹ_`.  This module only assembles the records; every law
-- is proved elsewhere, and `CategoricalCrypto.Machine.Monoidal` says where.
--
-- Only the three forward naturality squares are supplied; `monoidalHelper`
-- derives the `-to` halves as conjugates of them.  The forward associator
-- square is itself a conjugate, because the proved square is the inverse
-- associator's.
--
-- Everything downstream that only needs "a symmetric monoidal category of
-- machines" should go through the bundles at the bottom.  `Machine.UC` sets
-- `machines = Reverse-MonoidalCategory machine-monoidal-category` and opens
-- `Standard2.StdUC machines ℰ-tests`, so the abstract UC layer sees the
-- machine category reversed, with the grade on the right.
-- ============================================================================

module CategoricalCrypto.Machine.MonoidalCategory where

open import categorical-crypto.Prelude hiding (id; _∘_; Bifunctor)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal
  using (Monoidal; monoidalHelper; MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Forwarder
open import CategoricalCrypto.Machine.Monoidal.Interchange
open import CategoricalCrypto.Machine.Monoidal.Associator
open import CategoricalCrypto.Machine.Monoidal.Coherence
open import CategoricalCrypto.Machine.Monoidal.Unitors
open import CategoricalCrypto.Machine.Monoidal.Braiding

open Mor MachineCategory using (_≅_)
open MR MachineCategory using (conjugate-to)

machine-⊗-bifunctor : Bifunctor MachineCategory MachineCategory MachineCategory
machine-⊗-bifunctor = record
  { F₀           = λ (A , B) → A ⊗₀ B
  ; F₁           = λ (f , g) → f ⊗₁ g
  ; identity     = ⊗₁-id
  ; homomorphism = λ { {f = f , h} {g , k} → ⊗₁-interchange f g h k }
  ; F-resp-≈     = λ (φ , ψ) → ⊗₁-resp-≅ᴹ φ ψ
  }

unitorˡ-iso : ∀ {A} → (I ⊗₀ A) ≅ A
unitorˡ-iso = record { from = λ⇒ ; to = λ⇐ ; iso = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ } }

unitorʳ-iso : ∀ {A} → (A ⊗₀ I) ≅ A
unitorʳ-iso = record { from = ρ⇒ ; to = ρ⇐ ; iso = record { isoˡ = ρ-isoˡ ; isoʳ = ρ-isoʳ } }

associator-iso : ∀ {A B C} → ((A ⊗₀ B) ⊗₀ C) ≅ (A ⊗₀ (B ⊗₀ C))
associator-iso = record
  { from = ⊗-assoc ; to = ⊗-assoc⃖ ; iso = record { isoˡ = α-isoˡ ; isoʳ = α-isoʳ } }

machine-monoidal : Monoidal MachineCategory
machine-monoidal = monoidalHelper MachineCategory record
  { ⊗               = machine-⊗-bifunctor
  ; unit            = I
  ; unitorˡ         = unitorˡ-iso
  ; unitorʳ         = unitorʳ-iso
  ; associator      = associator-iso
  ; unitorˡ-commute = λ {_} {_} {f} → λ⇒-natural f
  ; unitorʳ-commute = λ {_} {_} {f} → ρ⇒-natural f
  ; assoc-commute   = λ {_} {_} {f} {_} {_} {g} {_} {_} {h} →
      ≅ᴹ-sym (conjugate-to associator-iso associator-iso (≅ᴹ-sym (⊗-assoc⃖-natural f g h)))
  ; triangle        = triangle
  ; pentagon        = pentagon
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

-- Ascribing a type to `curriedTensor machines` at the concrete machine
-- category costs 9 to 15 minutes of elaboration, so such triples are built
-- over an abstract monoidal category and instantiated afterwards; see
-- `Machine.UC.Kleisli`.
machine-symmetric-monoidal-category : SymmetricMonoidalCategory _ _ _
machine-symmetric-monoidal-category = record
  { U = MachineCategory ; monoidal = machine-monoidal ; symmetric = machine-symmetric }

machine-monoidal-category : MonoidalCategory _ _ _
machine-monoidal-category = SymmetricMonoidalCategory.monoidalCategory machine-symmetric-monoidal-category
