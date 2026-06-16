{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Final assembly of the strict soundness theorem, parameterised over the
-- SINGLE remaining residual `decodePˢ-⊗` (the ⊗-shape, pending the K-block
-- box-braid `KBlockσ`).  Everything else is concrete and axiom-free:
--
--   * part (I)ˢ  = `PartI.st-≈-decodePˢ decodePˢ-⊗`   (atomic/σ/∘/Agen done)
--   * part (II)ˢ = `PartII.decodePˢ-resp-iso`         (UNCONDITIONAL)
--   * the capstone `SoundnessStrict.soundness-strict`.
--
-- Discharging `decodePˢ-⊗` makes `soundness-assembled` unconditional, at
-- which point `SoundnessFullWired.soundness-full-wired` is re-pointed at it.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.SoundnessAssembly
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
  using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.SoundnessStrict sig _≟X_ as SST
import Categories.APROP.Hypergraph.Soundness.Strict.PartI           sig _≟X_ as PI
import Categories.APROP.Hypergraph.Soundness.Strict.PartII          sig _≟X_ as PII

module _
  (decodePˢ-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g)
  where

  soundness-assembled
    : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
  soundness-assembled =
    SST.soundness-strict (PI.st-≈-decodePˢ decodePˢ-⊗) PII.decodePˢ-resp-iso
