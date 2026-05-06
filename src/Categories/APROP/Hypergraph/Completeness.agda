{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Phase 3.5e — Completeness theorem.
--
-- Final assembly: from `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` derive `f ≈Term g`.  The
-- proof routes through:
--
--   1. ~decode-roundtrip-rel~  (constructive in DecodeRel modulo the
--                                bridge-α⇒-form-⊗-⊗ /
--                                decode-roundtrip-{Agen,σ} postulates):
--                                ~decode-rel f ≈Term bridge f~.
--   2. ~decode-rel-resp-≅ᴴ~    (postulated in DecodeRel): decode-rel
--                                preserves hypergraph iso.
--   3. ~bridge-cancel~         (constructive, here): the bridge has a
--                                two-sided inverse modulo ≈Term.
--
-- Refactor A (`decode-rel`) made the algorithmic `decode-{∘,⊗}-shape`
-- postulates (previously needed by `decode-roundtrip-{∘,⊗}`)
-- redundant: under decode-rel both shape lemmas are `refl`, so the
-- inductive cases compose without postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel; decode-rel-resp-≅ᴴ)

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
-- ~bridge-cancel~: ~bridge⁻¹ ∘ bridge ≈Term id~.  Pure category-theoretic
-- shuffling — associativity, the ~isoˡ~ laws on the unflatten-flatten
-- iso, and unitality.

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
-- The completeness theorem.

completeness
  : ∀ {A B} {f g : HomTerm A B}
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → f ≈Term g
completeness {f = f} {g = g} iso = begin
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
              (≈-Term-trans (decode-rel-resp-≅ᴴ f g iso)
                            (decode-roundtrip-rel g))
