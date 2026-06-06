{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The residual record for the two `decode-{∘,⊗}-shape` shape obligations:
--
--   decode-∘-shape : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
--                  → decode (g ∘ f) ≈Term decode g ∘ decode f
--
--   decode-⊗-shape : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
--                  → decode (f ⊗₁ g)
--                  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
--                       ∘ (decode f ⊗₁ decode g)
--                       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
--
-- `DecodeShapeResiduals` packages the two as record fields; consumers `open
-- DecodeShapeResiduals` and use `decode-{∘,⊗}-shape-inner` directly.  The
-- conclusions are kept at the `decode`-outer form (rather than at the inner
-- `proj₁ (decode-attempt-h*)` level) for ergonomics: an inner residual would
-- need the linearity witnesses and boundary equation as record indices.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core
  using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hCompose; hTensor; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; decode-attempt-Linear; decode-attempt-hCompose;
         decode-attempt-hTensor)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

record DecodeShapeResiduals : Set where
  field
    -- The `g ∘ f` shape: `decode (g ∘ f) ≈Term decode g ∘ decode f`.  The
    -- constructive content is the term-level decomposition of `process-edges`
    -- on the hCompose hypergraph + final-permute absorption.
    decode-∘-shape-inner
      : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
      → decode (g ∘ f) ≈Term decode g ∘ decode f

    -- The `f ⊗₁ g` shape: parallel, routed through `decode-attempt-hTensor`.
    decode-⊗-shape-inner
      : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
      → decode (f ⊗₁ g)
      ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
           ∘ (decode f ⊗₁ decode g)
           ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- Why the obligation is non-trivial: `decode` recurses on the term, but at
-- `g ∘ f` / `f ⊗₁ g` the hypergraph is `hCompose`/`hTensor` (with
-- `nE_G + nE_K` edges processed in `range`-order, plus a `final-permute` and
-- — for ⊗ — an `unflatten-++-≅` coherence wrapping).  The shape obligation
-- states that the composed decoder output factors back into the standalone
-- decoded sub-terms (the decoder is a "functor" modulo `≈Term`); the proof
-- inverts the process-edges machinery at the TERM level.
--
-- The two fields are referenced by `DecoderAgreementSafe.agda`'s
-- `DecoderAgreementAssumptions` (fields `decode-{∘,⊗}-shape-T`), wrapped via
-- `unapply-{∘,⊗}-shape`.
--------------------------------------------------------------------------------
