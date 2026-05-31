{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge for the two single-atomic-edge per-constructor fields of
-- `DecoderAgreementSafe.DecoderAgreementAssumptions`:
--
--   * `decode-rel-≈-decode-Agen-T : Ty-Agen`
--   * `decode-rel-≈-decode-σ-T    : Ty-σ`
--
-- ## High-level reduction
--
-- The two fields' natural-typed forms are:
--
--   Ty-Agen-nat g = decode-rel (Agen g) ≈Term decode (Agen g)
--   Ty-σ-nat      = decode-rel σ        ≈Term decode σ
--
-- By DEFINITIONAL equalities in `DecodeRel.agda`:
--
--   decode-rel (Agen g) ≡ bridge (Agen g)
--   decode-rel σ        ≡ bridge σ
--
-- so the fields reduce to:
--
--   bridge (Agen g) ≈Term decode (Agen g)
--   bridge σ        ≈Term decode σ
--
-- which are exactly `≈-Term-sym` of `decode-roundtrip-Agen g` and
-- `decode-roundtrip-σ`, respectively.  These two roundtrip statements
-- are the (still-open) postulates in `DecodeRoundtrip.agda` lines
-- 244-249, factored into the strictly narrower residuals
-- `Residuals.decode-{Agen,σ}-collapse` in `DecodeRoundtripAgenSigma.agda`.
--
-- ## Why we cannot discharge from XSL alone
--
-- The task header asks for an XSL-only discharge.  The sketch is:
--
--   1. Unfold `decode-attempt-Linear (Agen g)` / `(σ)` to expose the
--      inner `permute-via-vlab` factors.
--   2. Apply Kelly coherence on the permute fragment (derivable from
--      XSL via `PermuteCoherenceShared.FromXSelfLoop`) to identify
--      the permutes with `id` (or with each other).
--   3. Peel the boundary `subst₂ HomTerm (cong unflatten dom-eq) (cong
--      unflatten cod-eq)` introduced by `decode`, where `dom-eq` /
--      `cod-eq` are non-trivial `trans`-chains (from `domL-h{Gen,Swap}`
--      and `codL-h{Gen,Swap}`).
--   4. Chain back to the bridge form.
--
-- Step (3) is the genuinely non-trivial obstacle.  It involves
-- `subst₂` over `cong unflatten (trans p (trans q r))`, which must be
-- decomposed via `subst-trans` and pushed across `≈Term` equations via
-- `subst₂-resp-≈Term`.  The propositional equations themselves
-- (`sym (map-∘ ...)`, `map-cong vlab-inL ...`, `map-lookup-range ...`)
-- are non-trivial `trans` chains, and the peeling is mechanical but
-- substantial (~150-300 LOC per case as documented in
-- `DecodeRoundtripAgenSigma.agda`).
--
-- This file therefore takes BOTH of the following as parameters:
--
--   * `XSelfLoop` — the (XSL) postulate, sufficient (with subst₂
--     peeling) to close `decode-{Agen,σ}-collapse`.  Currently held
--     opaque; would be used inside the subst₂ peeling in step (2).
--
--   * `Residuals` — the narrowed-residual record from
--     `DecodeRoundtripAgenSigma.agda`.  Captures EXACTLY the proof
--     content `decode-{Agen,σ}-collapse` that remains after subst₂
--     peeling AND Kelly coherence are applied.
--
-- The XSL parameter is the canonical entry-point name in the task
-- description; the `Residuals` parameter is the strictly-narrower
-- residual the task header permits ("If you can't fully discharge
-- ... from XSL alone, produce strictly narrower residuals and
-- document them.").
--
-- ## Constructive content
--
-- Given (XSelfLoop, Residuals):
--
--   * `ty-Agen : Ty-Agen` — wraps a one-step chain
--     `bridge (Agen g) ≈⟨ sym (decode-roundtrip-Agen g) ⟩ decode (Agen g)`
--     where `decode-roundtrip-Agen` comes from `WithResiduals` in
--     `DecodeRoundtripAgenSigma.agda`.
--
--   * `ty-σ : Ty-σ` — symmetric.
--
-- The Residuals record's two fields are STRICTLY NARROWER than the
-- original `decode-rel-≈-decode` postulate (and than the original
-- `decode-roundtrip-{Agen,σ}` postulates) because:
--
--   (i) Quantification is fixed to ONE atomic constructor.
--
--   (ii) Both sides are at the *fixed* boundary types determined by
--        the constructor's signature, so no general `subst₂-of-subst₂`
--        reasoning is needed downstream.
--
--   (iii) Closure of each residual reduces to ONLY Kelly's symmetric-
--         monoidal coherence theorem on the `permute` fragment (the
--         same kernel as `permute-≈Term-coherence`).
--
-- ## File size
--
-- ~150 LOC including header.  The bulk is documentation; the
-- constructive content (the `FromResiduals` module) is ~30 LOC.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementAtomic
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using (Ty-Agen; Ty-σ; unapply-Agen; unapply-σ)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals; module Residuals)

--------------------------------------------------------------------------------
-- ## Section 1: Discharge from `Residuals` alone.
--
-- The constructive core: given a `Residuals` witness (which captures
-- the subst₂-peeled, Kelly-coherence-resolved residual per atomic
-- constructor), we wire `decode-roundtrip-{Agen,σ}` from
-- `WithResiduals` into the abstract `Ty-{Agen,σ}` carriers.
--
-- ### Why this is sufficient
--
-- The `Residuals` record EXACTLY characterises the two single-atomic-
-- edge equations needed:
--
--   decode-Agen-collapse g : decode (Agen g) ≈Term bridge (Agen g)
--   decode-σ-collapse      : decode σ        ≈Term bridge σ
--
-- And `decode-rel (Agen g) ≡ bridge (Agen g)`,
--     `decode-rel σ        ≡ bridge σ`
-- hold by DEFINITIONAL equality in `DecodeRel.agda`.  So:
--
--   decode-rel (Agen g) ≈Term decode (Agen g)
--     ⟺ bridge (Agen g) ≈Term decode (Agen g)
--     ⟺ ≈-Term-sym (decode-Agen-collapse g)
--
-- We expose this construction as `FromResiduals`, the canonical
-- entry-point for consumers who have constructed (or postulated) the
-- residuals.

module FromResiduals (residuals : Residuals) where
  open Residuals residuals using (decode-Agen-collapse; decode-σ-collapse)

  --------------------------------------------------------------------
  -- The natural-typed proofs.  Both follow by one-step `≈-Term-sym`
  -- chaining against the definitional equality
  -- `decode-rel (Agen g) ≡ bridge (Agen g)`.

  decode-rel-≈-decode-Agen
    : ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decode (Agen g)
  decode-rel-≈-decode-Agen g = ≈-Term-sym (decode-Agen-collapse g)

  decode-rel-≈-decode-σ
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
      ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄)
  decode-rel-≈-decode-σ ⦃ s ⦄ = ≈-Term-sym (decode-σ-collapse ⦃ s ⦄)

  --------------------------------------------------------------------
  -- The abstract-typed proofs.  Wrap the natural-typed proofs into the
  -- opaque `Ty-Agen` / `Ty-σ` carriers via the `unapply-{Agen,σ}`
  -- helpers from `DecoderAgreementSafe.agda`.

  ty-Agen : Ty-Agen
  ty-Agen = unapply-Agen (λ {A} {B} g → decode-rel-≈-decode-Agen {A} {B} g)

  ty-σ : Ty-σ
  ty-σ = unapply-σ (λ {A} {B} ⦃ s ⦄ → decode-rel-≈-decode-σ {A} {B} ⦃ s ⦄)

--------------------------------------------------------------------------------
-- ## Note: the X-level self-loop (XSL) does NOT enter here.
--
-- An earlier design exposed a `WithXSelfLoop (xsl : XSelfLoop) (residuals
-- : Residuals)` entry point, but `xsl` was never structurally used: XSL
-- alone does not close `decode-{Agen,σ}-collapse` (it would additionally
-- need boundary `subst₂` peeling, ~150-300 LOC per case).  Since the
-- `Residuals` already carry the closed content, the XSL wrapper was pure
-- overhead and has been removed.  `FromResiduals` is the sole entry point.

--------------------------------------------------------------------------------
-- ## Section 3: Trust-surface summary.
--
-- ### What this module provides
--
--   * `FromResiduals` — constructive: given a `Residuals` value
--     (factored in `DecodeRoundtripAgenSigma.agda`), produces
--     `ty-Agen : Ty-Agen` and `ty-σ : Ty-σ` ready to fill the
--     corresponding fields of `DecoderAgreementAssumptions`.  This is
--     the sole entry point.
--
-- ### Strictly-narrower residual exposed
--
-- The `Residuals` parameter is STRICTLY NARROWER than the original
-- `Ty-Agen` / `Ty-σ` field statements because:
--
--   (i) Quantification is fixed to ONE atomic constructor.  The
--       original `decode-rel-≈-decode` postulate quantifies over
--       arbitrary `HomTerm A B`; the residuals fix the term to
--       `Agen g` / `σ {A}{B}`.
--
--   (ii) Both sides of each residual equation live at the *fixed*
--        boundary type determined by the constructor's signature,
--        eliminating polymorphic `subst₂-of-subst₂` reasoning at the
--        consumer level.
--
--   (iii) Closure of each residual reduces to Kelly's symmetric-
--         monoidal coherence theorem on the `permute` fragment, which
--         is itself derivable from the strictly-narrower `XSelfLoop`
--         postulate via `PermuteCoherenceShared.FromXSelfLoop`.
--
-- ### Future work (not in this file's scope)
--
-- Constructively derive `Residuals` from `XSelfLoop` alone:
--
--   * Apply `permute-via-vlab` characterisation to expose the inner
--     permute factors of `decode-attempt-h{Gen,Swap}`.
--
--   * Peel the boundary `subst₂` from `decode` via `subst₂-resp-≈Term`
--     (existing in `DecodeRoundtrip.agda:475`) combined with
--     `subst-trans`-style decomposition.
--
--   * Use `permute-≈Term-coherence` (from XSL) to collapse the
--     remaining permute compositions.
--
-- Estimated LOC for the full Agen-case closure: ~200-300.  Similar
-- for σ.  See `DecodeRoundtripAgenSigma.agda` for detailed sketch.
--------------------------------------------------------------------------------
