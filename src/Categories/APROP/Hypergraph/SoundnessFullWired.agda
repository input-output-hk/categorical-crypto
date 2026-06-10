{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Soundness theorem, wired through `DecodeRelRespIsoWired`.
--
-- `DecodeRelRespIsoWired.decode-rel-resp-iso` proves
--   ⟪f⟫ ≅ᴴ ⟪g⟫  →  decode-rel f ≈Term decode-rel g
-- axiom-free (its Kelly residual is the proven
-- `FaithfulnessInductive.faithfulness`).  Composed with the
-- `decode-roundtrip-rel` round-trip and the `bridge`/`bridge⁻¹`
-- cancellation, it yields `f ≈Term g`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.SoundnessFullWired
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
open import Categories.APROP.Hypergraph.Soundness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)

import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeRelRespIsoWired
  sig _≟X_ as DRRIW

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
  soundness-full-wired
    : ∀ {A B} {f g : HomTerm A B}
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → f ≈Term g
  soundness-full-wired {f = f} {g = g} iso = begin
    f
      ≈⟨ bridge-cancel f ⟨
    bridge⁻¹ (bridge f)
      ≈⟨ ∘-resp-≈ FM.Equiv.refl (∘-resp-≈ bf≈bg FM.Equiv.refl) ⟩
    bridge⁻¹ (bridge g)
      ≈⟨ bridge-cancel g ⟩
    g ∎
    where
      bf≈bg : bridge f ≈Term bridge g
      bf≈bg = ≈-Term-trans (≈-Term-sym (decode-roundtrip-rel f))
                (≈-Term-trans (DRRIW.decode-rel-resp-iso f g iso)
                              (decode-roundtrip-rel g))
