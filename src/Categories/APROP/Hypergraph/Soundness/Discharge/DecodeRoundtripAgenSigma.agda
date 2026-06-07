{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Narrowed residuals for the atomic constructor cases of axiom F
-- (`decode-rel-≈-decode`): `decode X ≈Term bridge X` for `X ∈ {Agen g, σ}`.
--
--   `decode X = subst₂ HomTerm … (proj₁ (decode-attempt-Linear X))`
--   `bridge X = ≅.from (uf-fl B) ∘ X ∘ ≅.to (uf-fl A)`
--
-- where the boundary `subst₂` wraps the algorithm's output along the
-- non-trivial `cong unflatten (⟪⟫-{dom,cod}L X)` paths.  Each residual is
-- narrower than the original `decode-roundtrip`: it fixes a specific
-- constructor (no quantification over `HomTerm A B`), so closing it needs
-- only Kelly coherence on the `permute` fragment.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.DecodeRoundtripAgenSigma
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (decode; bridge)

record Residuals : Set where
  field
    decode-Agen-collapse
      : ∀ {A B} (g : mor A B) → decode (Agen g) ≈Term bridge (Agen g)

    decode-σ-collapse
      : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
      → decode (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)
