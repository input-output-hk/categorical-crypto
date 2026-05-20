{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Completeness theorem, threaded through the inductive
-- `decode-rel-resp-≅ᴴ-full` from `DecodeRel/Inductive.agda` instead of
-- the top-level `decode-rel-resp-≅ᴴ` postulate in `DecodeRel.agda`.
--
-- The only remaining postulates on the path to `completeness-full` are
-- the seven narrow ones in `DecodeRel/Inductive.agda`'s subordinate
-- modules — see that file for the inventory.
--
-- This module is parameterized by `APROPSignatureDec` (required by
-- the Agen-Agen case in Phase 1's atomic dispatcher).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.CompletenessFull
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
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
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive sig-dec
  using (decode-rel-resp-≅ᴴ-full)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Inverse bridge: pre/post-compose with the `to`/`from` of
-- ~unflatten-flatten-≈~ in the opposite direction from `bridge`.

bridge⁻¹
  : ∀ {A B}
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  → HomTerm A B
bridge⁻¹ {A} {B} h =
  _≅_.to (unflatten-flatten-≈ B) ∘ h ∘ _≅_.from (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- `bridge-cancel`: `bridge⁻¹ ∘ bridge ≈Term id`.

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
-- The completeness theorem.  Uses the inductive `decode-rel-resp-≅ᴴ-full`
-- in place of the original `decode-rel-resp-≅ᴴ` postulate, so the only
-- remaining postulates on this path are the narrow ones in the
-- `DecodeRel/Inductive.agda` subordinate modules.

completeness-full
  : ∀ {A B} {f g : HomTerm A B}
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → f ≈Term g
completeness-full {f = f} {g = g} iso = begin
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
              (≈-Term-trans (decode-rel-resp-≅ᴴ-full f g iso)
                            (decode-roundtrip-rel g))
