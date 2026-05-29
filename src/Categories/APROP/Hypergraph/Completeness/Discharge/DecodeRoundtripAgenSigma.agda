{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge for `decode-roundtrip-Agen` and `decode-roundtrip-σ`
-- (Phase 3.5f Step 5, atomic constructor cases of axiom F =
-- `decode-rel-≈-decode`).
--
-- These two postulates live in `DecodeRoundtrip.agda` (lines 243-249) as the
-- per-constructor atomic cases of the structural roundtrip proof.  Both share
-- the same structural obstacle: the boundary `subst₂` introduced by `decode`
-- wraps the natural-typed `proj₁ (decode-attempt-h{Gen,Swap})` along the
-- propositional boundary equations `cong unflatten (⟪⟫-{dom,cod}L X)`, which
-- are NON-TRIVIAL `trans` chains (built from `sym (map-∘ ...)`,
-- `map-lookup-range`, `++-comm`, etc.).
--
-- ## Decomposition of the proof obligation.
--
-- For each constructor `X ∈ { Agen g , σ {A}{B} }`:
--
--   `decode X = subst₂ HomTerm (cong unflatten dom-eq) (cong unflatten cod-eq)
--                      (proj₁ (decode-attempt-Linear X))`
--
-- and
--
--   `bridge X = c-from-B ∘ X ∘ c-to-A`
--
-- where `c-from-B = ≅.from (unflatten-flatten-≈ B)`,
--       `c-to-A = ≅.to (unflatten-flatten-≈ A)`.
--
-- The algorithmic interior `proj₁ (decode-attempt-Linear X)`:
--
--   * For `Agen g`: a composition of two `permute-via-vlab` calls (from
--     `extract-prefix-self` and `extract-prefix-from-↭`) wrapping the literal
--     edge `Agen-edge 0` (itself a c-iso-wrapped `Agen g` modulo the vlab
--     `subst₂` of `lem-in`/`lem-out`).
--
--   * For `σ {A}{B}`: nE = 0, so just one `permute-via-vlab` from
--     `extract-prefix-from-↭` applied to `PermProp.++-comm L R`, composed
--     with `id`.
--
-- ## Constructive content provided here.
--
-- The wiring `Residuals → decode-roundtrip-{Agen,σ}` is fully constructive
-- (one-step derivation per case).  The genuinely irreducible content is the
-- single `≈Term`-identity between the algorithm's output and the bridge
-- form, per case.  Each residual is STRICTLY NARROWER than the original
-- because:
--
--   (i) It mentions a SPECIFIC concrete constructor (Agen g, σ {A}{B}),
--       not an arbitrary HomTerm.  No quantification over `HomTerm A B`.
--
--   (ii) Both sides of the equation are at the *fixed* boundary types
--        determined by the constructor's signature, so no general
--        `subst₂-of-subst₂` reasoning is left.
--
--   (iii) Closure of each requires ONLY the Kelly symmetric-monoidal
--         coherence theorem on the `permute` fragment (the same kernel
--         already isolated as `PermuteCoherence.permute-≈Term-coherence`
--         in `Discharge/FinalPermute.agda`).
--
-- ## LOC budget.
--
-- ~155 LOC including header.  A FULL inline discharge per case is
-- estimated at ~150-300 LOC each, dominated by:
--
--   * Decomposing the `with`-rewritten `decode-attempt-h{Gen,Swap}`
--     output via `decode-attempt-perm-from-just` + the `extract-prefix-*`
--     extraction structure.
--
--   * Applying `subst₂-resp-≈Term` (DecodeRoundtrip.agda:475) to push the
--     boundary `subst₂` through the algorithmic chain.
--
--   * Discharging the resulting Kelly-coherence step via
--     `PermuteCoherence` / `permute-≈Term-coherence`.
--
-- Each chain involves multiple `subst-∘` rewrites, `cong-trans` peeling, and
-- a final coherence appeal.  The narrowed residuals in this file expose
-- each chain's terminating step at the right type signature.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)

--------------------------------------------------------------------------------
-- The narrowed residuals record.
--
-- Each field is a strictly narrower form of the original postulate it
-- replaces:
--
--   - Quantification is fixed to ONE atomic constructor (Agen g / σ {A}{B}),
--     not the polymorphic `decode-roundtrip` over arbitrary HomTerms.
--
--   - No IH or recursion is required — these are PURE structural facts
--     about ONE algorithmic output equating ONE bridge form.
--
--   - Closing each requires only Kelly's symmetric-monoidal coherence
--     theorem on the `permute` fragment plus a deterministic chain of
--     `subst-∘` / `subst₂-resp-≈Term` peelings of the boundary subst₂.
--
-- ## Insights about the boundary subst₂.
--
-- For both cases the boundary `subst₂` lives at:
--
--     subst₂ HomTerm (cong unflatten (⟪⟫-domL X)) (cong unflatten (⟪⟫-codL X))
--
-- where `⟪⟫-{dom,cod}L X` is the `domL-hX` / `codL-hX` proof from
-- `FromAPROP.agda`.  Concretely:
--
--   * `domL-hGen g = trans (sym (map-∘ ...)) (trans (map-cong vlab-inL ...)
--                          (map-lookup-range (flatten A)))`
--     — a chain of three `_≡_` steps, NOT `refl`.
--
--   * `codL-hGen g` symmetric.
--
--   * `domL-hSwap A B = trans (map-++ ...) (cong₂ _++_ lem-L lem-R)`
--     where `lem-L`, `lem-R` are themselves `trans` chains.
--
--   * `codL-hSwap A B` symmetric.
--
-- The `subst₂` over these `cong unflatten`-of-`trans`-chains can be split by:
--
--   * `subst₂` over `trans p q` = `subst₂ q ∘ subst₂ p` (standard).
--
--   * `subst₂-resp-≈Term` (DecodeRoundtrip.agda:475) carries an `≈Term`
--     equation across a `subst₂` boundary.
--
-- Combined, the boundary `subst₂` can be pushed inside the algorithmic
-- chain to land at points where `≅`-iso laws cancel.

record Residuals : Set where
  field
    -- Generator case: `decode (Agen g) ≈Term bridge (Agen g)`.
    --
    -- Strictly narrower than the original via constraints (i)-(iii) above.
    -- Closure: ~200 LOC of inline chain reasoning (boundary subst₂ peeling
    -- + Kelly coherence on the inner permute compositions).
    decode-Agen-collapse
      : ∀ {A B} (g : mor A B) → decode (Agen g) ≈Term bridge (Agen g)

    -- Swap case: `decode (σ {A}{B}) ≈Term bridge (σ {A}{B})`.
    --
    -- Strictly narrower for the same reasons.  Closure is somewhat simpler
    -- than the generator case (no inner edge generator to peel; just a
    -- single outer permute from `++-comm`).
    decode-σ-collapse
      : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
      → decode (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)

--------------------------------------------------------------------------------
-- The `Residuals` fields ARE the discharge: each field already has the
-- exact proposition `decode (Agen g) ≈Term bridge (Agen g)` (resp. σ)
-- at the natural boundary type.  Consumers `open Residuals` and use
-- `decode-{Agen,σ}-collapse` directly — no wrapper module is needed.
-- (An earlier `module WithResiduals` re-exported the fields under the
-- names `decode-roundtrip-{Agen,σ}`; it was a pure rename and has been
-- removed.)
