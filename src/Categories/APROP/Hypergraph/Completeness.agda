{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5e — Completeness theorem.
--
-- Final assembly: from `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` derive `f ≈Term g`.  The
-- proof routes through:
--
--   1. ~decode-roundtrip~   (postulated in Decoder): on translated
--                            terms, ~decode ⟪ f ⟫ ≈Term bridge f~.
--   2. ~decode-resp-≅ᴴ~     (postulated in Decoder): decode preserves
--                            hypergraph iso.
--   3. ~bridge-cancel~      (constructive, here): the bridge has a
--                            two-sided inverse modulo ≈Term.
--
-- Step 3 is purely categorical (associativity + iso laws on
-- ~unflatten-flatten-≈~).  Steps 1 and 2 are the genuinely hard
-- postulates that close the syntactic completeness gap.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.Decoder sig
  using (decode; bridge; decode-roundtrip; decode-resp-≅ᴴ)

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
    bf≈bg = ≈-Term-trans (≈-Term-sym (decode-roundtrip f))
              (≈-Term-trans (decode-resp-≅ᴴ iso) (decode-roundtrip g))
