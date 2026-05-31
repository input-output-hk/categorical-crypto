{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `Ty-ρ⇒` and `Ty-ρ⇐` (two of the 11 per-constructor fields
-- of `DecoderAgreementAssumptions`) from `Ty-⊗-shape` plus a small
-- residual record (`RhoShapeResidual`) of two shape-postulates currently
-- still open in `DecodeRoundtrip.agda`.
--
-- ## Strategy
--
-- For X ∈ {ρ⇒, ρ⇐}:
--
--   1. `decode-rel (X {A}) = bridge (X {A})` (definitional, from
--      `DecodeRel.agda` lines 74-75).
--   2. Therefore `decode-rel (X) ≈Term decode (X)` reduces to proving
--      `bridge (X {A}) ≈Term decode (X {A})`.
--   3. Chain (mirroring `decode-roundtrip-ρ⇒` in `DecodeRoundtrip.agda`
--      lines 1888-1899):
--
--        decode (ρ⇒ {A})
--          ≈⟨ decode-ρ⇒-shape A ⟩
--        subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
--                            (decode (id {A ⊗₀ unit}))
--          ≈⟨ subst₂-resp-≈Term refl (++-identityʳ (flatten A))
--                                (decode-id-is-id (A ⊗₀ unit)) ⟩
--        subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
--          ≈⟨ ρ⇒-coherence A ⟩
--        bridge (ρ⇒ {A})
--
--   4. Use `≈-Term-sym` to reverse the chain into `bridge → decode`,
--      then `≈-Term-trans` with `≈-Term-refl` for the definitional
--      `decode-rel X = bridge X`.
--
-- ## Inputs
--
--   * `t⊗ : Ty-⊗-shape` — supplies the inductive `A ⊗₀ B` step of
--     `decode-id-is-id`, exactly as in
--     `Discharge/DecoderAgreementCases.agda`'s `FromShape` module.
--   * `rsr : RhoShapeResidual` — wraps the two `decode-ρ⇒-shape` /
--     `decode-ρ⇐-shape` propositional equations, which are postulated
--     in `DecodeRoundtrip.agda:438-455` (under de-indexing).  Their
--     discharge requires `cong-trans`, `subst₂-trans-cod`/`-dom`, and
--     `subst₂-refl-{dom,cod}-≡` over `⟪⟫-codL (ρ⇒)` / `⟪⟫-domL (ρ⇐)`,
--     which factor as `≡-trans codL-hId outer-eq` for ρ.  We surface
--     them as a residual rather than rederiving inline (~150 LOC each).
--
-- ## Outputs
--
--   * `ty-ρ⇒ : Ty-ρ⇒`
--   * `ty-ρ⇐ : Ty-ρ⇐`
--
-- ## Residuals
--
-- Exactly two open propositional equations, packaged in
-- `RhoShapeResidual`.  These mirror `DecodeRoundtrip.agda:448-455`.
--
-- The bridge form of each, the boundary `subst₂` decomposition, and
-- the `ρ⇒`/`ρ⇐` list-coherence side are all already constructive in
-- `DecodeRoundtripSafe.agda`.  The only remaining propositional gap is
-- the algorithmic `decode-X-shape` characterisation.
--
-- ## Inheritance from `DecoderAgreementCases.FromShape`
--
-- We do NOT re-prove `decode-id-is-id` here; instead we open the
-- existing `FromShape t⊗` module from `DecoderAgreementCases` and reuse
-- its polymorphic `decode-id-is-id`.  The chains for ρ⇒/ρ⇐ then become
-- pure 3-step combinators (shape + IH + coherence).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( Ty-⊗-shape
        ; Ty-ρ⇒; Ty-ρ⇐
        ; unapply-ρ⇒; unapply-ρ⇐
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( ≡⇒≈Term
        ; subst₂-resp-≈Term
        ; ρ⇒-coherence
        ; ρ⇐-coherence
        )
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig

open import Categories.Category using (Category)

open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Residual: the two `decode-X-shape` propositional equations.
--
-- These are postulated in `DecodeRoundtrip.agda:448-455`.  Each is a
-- characterisation of how `decode (X)` factors through a boundary
-- `subst₂` over `++-identityʳ (flatten A)`, with `decode (id {A ⊗₀ unit})`
-- as the underlying "inner" term.
--
-- Discharging these constructively requires unfolding
-- `decode-attempt-Linear (X)` against `⟪ X ⟫ = hId (A ⊗₀ unit)`, then
-- pushing the boundary `subst₂` over the `≡-trans codL-hId outer-eq`
-- structure of `⟪⟫-codL` (or `⟪⟫-domL`).  The proof outline uses
-- `cong-trans`, `subst₂-trans-{cod,dom}`, and `subst₂-refl-{dom,cod}-≡`.

record RhoShapeResidual : Set where
  field
    decode-ρ⇒-shape
      : ∀ A → decode (ρ⇒ {A})
           ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                    (decode (id {A ⊗₀ unit}))
    decode-ρ⇐-shape
      : ∀ A → decode (ρ⇐ {A})
           ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                    (decode (id {A ⊗₀ unit}))

--------------------------------------------------------------------------------
-- ## `FromShape t⊗ rsr`: derive `Ty-ρ⇒` and `Ty-ρ⇐`.
--
-- The chain for each follows `decode-roundtrip-ρ⇒` /
-- `decode-roundtrip-ρ⇐` in `DecodeRoundtrip.agda:1888-1912`:
--
--   bridge (X {A})
--     ≈⟨ X-coherence A ⟩⟨reversed⟩
--   subst₂ ... id
--     ≈⟨ subst₂-resp-≈Term ... (≈-Term-sym (decode-id-is-id (A ⊗₀ unit))) ⟩
--   subst₂ ... (decode (id {A ⊗₀ unit}))
--     ≈⟨ ≡⇒≈Term (sym (decode-X-shape A)) ⟩
--   decode (X {A})
--
-- Then `decode-rel (X {A}) = bridge (X {A})` definitionally, so
-- `decode-rel (X) ≈Term decode (X)` follows by transitivity.
--
-- (We use the forward chain `bridge → decode` then `≈-Term-sym` to
-- arrive at the `decode-rel X ≈ decode X` signature required by `Ty-X`.)

module FromShape (t⊗ : Ty-⊗-shape) (rsr : RhoShapeResidual) where

  open RhoShapeResidual rsr
  open Cases-sig.FromShape t⊗ using (decode-id-is-id)

  -- `bridge (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})`.  Mirror of
  -- `≈-Term-sym decode-roundtrip-ρ⇒` from `DecodeRoundtrip.agda:1888-1899`.
  bridge-ρ⇒-≈-decode : ∀ A → bridge (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})
  bridge-ρ⇒-≈-decode A = begin
    bridge (ρ⇒ {A})
      ≈⟨ ρ⇒-coherence A ⟨
    subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
      ≈⟨ subst₂-resp-≈Term refl (++-identityʳ (flatten A))
                            (decode-id-is-id (A ⊗₀ unit)) ⟨
    subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                         (decode (id {A ⊗₀ unit}))
      ≈⟨ ≡⇒≈Term (decode-ρ⇒-shape A) ⟨
    decode (ρ⇒ {A}) ∎

  -- `bridge (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})`.  Mirror of
  -- `≈-Term-sym decode-roundtrip-ρ⇐` from `DecodeRoundtrip.agda:1901-1912`.
  bridge-ρ⇐-≈-decode : ∀ A → bridge (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})
  bridge-ρ⇐-≈-decode A = begin
    bridge (ρ⇐ {A})
      ≈⟨ ρ⇐-coherence A ⟨
    subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
      ≈⟨ subst₂-resp-≈Term (++-identityʳ (flatten A)) refl
                            (decode-id-is-id (A ⊗₀ unit)) ⟨
    subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                         (decode (id {A ⊗₀ unit}))
      ≈⟨ ≡⇒≈Term (decode-ρ⇐-shape A) ⟨
    decode (ρ⇐ {A}) ∎

  -- The two closed `Ty-X` values.
  --
  -- `decode-rel (ρ⇒ {A}) = bridge (ρ⇒ {A})` definitionally
  -- (`DecodeRel.agda:74`), so Agda accepts `bridge-ρ⇒-≈-decode A`
  -- where a `decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})` is needed.

  ty-ρ⇒ : Ty-ρ⇒
  ty-ρ⇒ = unapply-ρ⇒ (λ {A} → bridge-ρ⇒-≈-decode A)

  ty-ρ⇐ : Ty-ρ⇐
  ty-ρ⇐ = unapply-ρ⇐ (λ {A} → bridge-ρ⇐-≈-decode A)

--------------------------------------------------------------------------------
-- ## Summary
--
-- This module discharges 2 of 11 `DecoderAgreementAssumptions` fields:
--
--   * `Ty-ρ⇒`, `Ty-ρ⇐`
--
-- Constructive from:
--
--   * `Ty-⊗-shape` (one of the 11 sibling fields; needed for
--     `decode-id-is-id` at `A ⊗₀ B`).
--   * Two propositional residuals `decode-ρ⇒-shape` and
--     `decode-ρ⇐-shape`, mirroring `DecodeRoundtrip.agda:448-455`.
--     These are SEPARATELY-SUPPLIED — packaged as a `RhoShapeResidual`
--     record.
--
-- The constructive content used here:
--
--   * `ρ⇒-coherence`, `ρ⇐-coherence` (from `DecodeRoundtripSafe`,
--     which itself depends on `bridge-ρ⇒-form` + `ρ⇒-coh-list`).
--   * `subst₂-resp-≈Term`, `≡⇒≈Term` (from `DecodeRoundtripSafe`).
--   * `decode-id-is-id` (from `DecoderAgreementCases.FromShape`,
--     parametrised on `t⊗`).
--   * Definitional `decode-rel (X {A}) = bridge (X {A})` (from
--     `DecodeRel.agda`).
--
-- ## Remaining for the broader effort
--
-- To assemble the full `DecoderAgreementAssumptions`, the remaining 6
-- fields (`Ty-Agen`, `Ty-σ`, `Ty-α⇒`, `Ty-α⇐`, `Ty-∘-shape`,
-- `Ty-⊗-shape`) plus the 2 propositional residuals must be supplied.
-- After that, `Ty-id`, `Ty-λ⇒`, `Ty-λ⇐` (3 fields, via
-- `DecoderAgreementCases.FromShape`) and `Ty-ρ⇒`, `Ty-ρ⇐` (2 fields,
-- this module) are all derivable from `Ty-⊗-shape` + the residual.
--
-- That brings the constructive coverage to 5/11 once `Ty-⊗-shape` and
-- the `RhoShapeResidual` are in hand.
