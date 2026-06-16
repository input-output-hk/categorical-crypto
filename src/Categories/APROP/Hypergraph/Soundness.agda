{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Soundness theorem, re-pointed at the STRICTIFIED pipeline.
--
-- `soundness` now delegates to
-- `Strict.SoundnessAssembly.soundness-assembled` fed the unconditional
-- strict ⊗-shape `Strict.TensorKBlockFinal.decodePˢ-⊗-concrete`.  That path
-- proves `⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g` entirely inside the presented strict SMC
-- `S` (part (I)ˢ `st ≈ˢ decodePˢ` + part (II)ˢ `decodePˢ`-iso-invariance,
-- reflected via `embF`/`st-roundtrip` + the `bridge` cancellation), with the
-- single deep Kelly residual `permˢ-K` discharged axiom-free.  The TYPE is
-- unchanged, so all downstream consumers are unaffected.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Soundness
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_)
open APROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (bridge)

import Categories.APROP.Hypergraph.Soundness.Strict.SoundnessAssembly sig _≟X_ as SA
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlockFinal sig _≟X_ as TKF

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Inverse bridge + cancellation.

bridge⁻¹
  : ∀ {A B}
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  → HomTerm A B
bridge⁻¹ {A} {B} h =
  _≅_.to (unflatten-flatten-≈ B) ∘ h ∘ _≅_.from (unflatten-flatten-≈ A)

bridge-cancel : ∀ {A B} (f : HomTerm A B) → bridge⁻¹ (bridge f) ≈Term f
bridge-cancel {A} {B} f = begin
  to-B ∘ (from-B ∘ (f ∘ to-A)) ∘ from-A
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  to-B ∘ from-B ∘ (f ∘ to-A) ∘ from-A
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
  to-B ∘ from-B ∘ f ∘ to-A ∘ from-A
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-flatten-≈ A) ⟩
  to-B ∘ from-B ∘ f ∘ id
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.identityʳ ⟩
  to-B ∘ from-B ∘ f
    ≈⟨ FM.sym-assoc ⟩
  (to-B ∘ from-B) ∘ f
    ≈⟨ _≅_.isoˡ (unflatten-flatten-≈ B) ⟩∘⟨refl ⟩
  id ∘ f
    ≈⟨ FM.identityˡ ⟩
  f ∎
  where
    from-A = _≅_.from (unflatten-flatten-≈ A)
    to-A   = _≅_.to   (unflatten-flatten-≈ A)
    from-B = _≅_.from (unflatten-flatten-≈ B)
    to-B   = _≅_.to   (unflatten-flatten-≈ B)

--------------------------------------------------------------------------------
-- The soundness theorem.

opaque
  soundness
    : ∀ {A B} {f g : HomTerm A B}
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → f ≈Term g
  soundness = SA.soundness-assembled TKF.decodePˢ-⊗-concrete
