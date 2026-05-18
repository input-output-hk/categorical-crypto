{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge of `decode-rel-resp-≅ᴴ-⊗∘` from `Inductive.agda`.
--
-- This is the symmetric direction of `decode-rel-resp-≅ᴴ-∘⊗`.  We derive
-- it directly by flipping the iso with `sym-≅ᴴ` and the conclusion with
-- `≈-Term-sym`.
--
-- NOTE: this discharge shifts the burden onto `decode-rel-resp-≅ᴴ-∘⊗`,
-- which is itself currently a postulate in `Inductive.agda` (slated for
-- discharge in the sibling file `Discharge/CrossOC.agda`).  Once that
-- file lands, this lemma becomes fully constructive.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.CrossCO
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive sig-dec
  using (decode-rel-resp-≅ᴴ-∘⊗)

--------------------------------------------------------------------------------
-- Main lemma: ⊗∘ direction, derived from the ∘⊗ direction.

decode-rel-resp-≅ᴴ-⊗∘
  : ∀ {Ap Aq Bp Bq X}
      (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
      (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
  → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
  → decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)
decode-rel-resp-≅ᴴ-⊗∘ p q g f iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-∘⊗ g f p q (sym-≅ᴴ iso))
