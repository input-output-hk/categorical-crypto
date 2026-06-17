{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Final assembly of the strict soundness theorem, parameterised over the
-- ⊗-shape `decodePˢ-⊗`.  Everything else is concrete and axiom-free:
--
--   * part (I)ˢ  = `PartI.st-≈-decodePˢ decodePˢ-⊗`   (atomic/σ/∘/Agen done)
--   * part (II)ˢ = `PartII.decodePˢ-resp-iso`         (UNCONDITIONAL)
--   * the capstone `SoundnessParam.soundness-strict`.
--
-- `decodePˢ-⊗` is now supplied UNCONDITIONALLY by
-- `Strict.Tensor.TensorKBlockFinal.decodePˢ-⊗-concrete` (the ⊗-shape's
-- box-braid `KBlockσ` is discharged there, ZERO postulates).  The capstone
-- `Soundness.soundness` is already re-pointed at `soundness-assembled` fed
-- with that concrete witness; this module stays correctly parametric so the
-- ⊗-shape remains a clean, single dependency.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Soundness
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.SoundnessParam sig _≟X_ as SST
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
