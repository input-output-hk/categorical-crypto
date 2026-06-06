{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Completeness theorem, wired through the standalone `DecodeRelRespIsoWired`
-- chain instead of the `Build`/`DecodeRel.Inductive` route used by
-- `CompletenessFull.agda`.
--
-- `DecodeRelRespIsoWired.decode-rel-resp-iso` proves
--   ⟪f⟫ ≅ᴴ ⟪g⟫  →  decode-rel f ≈Term decode-rel g
-- with NO assumptions: the Kelly residual it needs is the PROVEN
-- `FaithfulnessInductive.faithfulness` (constructive symmetric-monoidal
-- permutation coherence).  Composed here with the proven `decode-roundtrip-rel`
-- round-trip and the `bridge`/`bridge⁻¹` cancellation, it yields the
-- completeness theorem `f ≈Term g`, FULLY AXIOM-FREE.
--
-- This module is `--safe --with-K` and postulate-free (the whole wired chain
-- is `--safe`).  It is the wired analogue of `CompletenessFull.completeness-full`
-- — the body is identical except that `decode-rel-resp-iso` replaces the
-- `Build`-derived `decode-rel-resp-≅ᴴ-full`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.CompletenessFullWired
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_)
open APROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)

-- The standalone faithfulness chain.  Its Kelly residual is now the PROVEN
-- `FaithfulnessInductive.faithfulness`, so this needs no assumption.
import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelRespIsoWired
  sig _≟X_ as DRRIW

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Inverse bridge + cancellation (verbatim from `CompletenessFull.agda`).

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
-- The completeness theorem — fully axiom-free.

completeness-full-wired
  : ∀ {A B} {f g : HomTerm A B}
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → f ≈Term g
completeness-full-wired {f = f} {g = g} iso = begin
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
