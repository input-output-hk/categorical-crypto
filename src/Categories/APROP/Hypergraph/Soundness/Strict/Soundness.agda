{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The re-pointed soundness theorem, via the strictified pipeline:
--
--     soundness-strict : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
--
-- assembled from
--   * part (I)ˢ   `st-≈-decodePˢ : st h ≈ˢ decodePˢ h`        (Strict.PartI)
--     at the unconditional ⊗-shape `TensorKBlockFinal.decodePˢ-⊗-concrete`
--     (its K-block box-braid `KBlockσ` discharged there, ZERO postulates);
--   * part (II)ˢ  `decodePˢ-resp-iso : ⟪f⟫≅ᴴ⟪g⟫ → decodePˢ f ≈ˢ decodePˢ g`
--     (Strict.PartII, unconditional);
--   * `embF-resp-≈ˢ` + `st-roundtrip` (Strict.Boundary)
--   * `bridge-cancel` (the `unflatten-flatten-≈` iso cancellation).
--
-- Everything here is concrete; the root `Soundness.agda` only re-exports
-- `soundness-strict` under its final name.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Soundness
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; bridge)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (embF; embF-resp-≈ˢ; st-roundtrip)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.PartI  sig _≟X_ as PI
import Categories.APROP.Hypergraph.Soundness.Strict.PartII sig _≟X_ as PII
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlockFinal sig _≟X_
  as TKF

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal
  using (pullʳ; cancelʳ; cancelˡ)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- Inverse bridge + cancellation.  This is their only home.

bridge⁻¹
  : ∀ {A B}
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  → HomTerm A B
bridge⁻¹ {A} {B} h =
  _≅_.to (unflatten-flatten-≈ B) ∘ h ∘ _≅_.from (unflatten-flatten-≈ A)

-- the A-side pair cancels under `to-B ∘ (from-B ∘ _)`, which then cancels too.
bridge-cancel : ∀ {A B} (f : HomTerm A B) → bridge⁻¹ (bridge f) ≈Term f
bridge-cancel {A} {B} f =
  (refl⟩∘⟨ pullʳ (cancelʳ (_≅_.isoˡ (unflatten-flatten-≈ A))))
  ○ cancelˡ (_≅_.isoˡ (unflatten-flatten-≈ B))

--------------------------------------------------------------------------------
-- The strict soundness theorem, from its two halves.

private
  part-Iˢ  = PI.st-≈-decodePˢ TKF.decodePˢ-⊗-concrete
  part-IIˢ = PII.decodePˢ-resp-iso

-- the strict core: `st f ≈ˢ st g` from the hypergraph iso
st-resp-iso : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → st f ≈ˢ st g
st-resp-iso f g iso =
  ≈-trans (part-Iˢ f) (≈-trans (part-IIˢ f g iso) (≈-sym (part-Iˢ g)))

-- transported to the free SMC: `bridge f ≈Term bridge g`
bridge-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → bridge f ≈Term bridge g
bridge-resp-iso f g iso = begin
  bridge f          ≈⟨ st-roundtrip f ⟨
  embF (st f)       ≈⟨ embF-resp-≈ˢ (st-resp-iso f g iso) ⟩
  embF (st g)       ≈⟨ st-roundtrip g ⟩
  bridge g          ∎

-- the headline theorem
soundness-strict : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
soundness-strict {f = f} {g = g} iso = begin
  f                       ≈⟨ bridge-cancel f ⟨
  bridge⁻¹ (bridge f)     ≈⟨ refl⟩∘⟨ (bridge-resp-iso f g iso ⟩∘⟨refl) ⟩
  bridge⁻¹ (bridge g)     ≈⟨ bridge-cancel g ⟩
  g ∎
