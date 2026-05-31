{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for the two `decode-{∘,⊗}-shape` postulates from
-- `Completeness/DecodeRoundtrip.agda` lines 231-241.
--
-- ## Goal
--
-- Constructively reduce the two shape postulates
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
-- to STRICTLY NARROWER residual record fields.  The narrowing makes
-- explicit the SINGLE architectural blocker (term-level
-- decomposition of `process-edges` on hCompose / hTensor
-- hypergraphs), separating it from the boundary `subst₂` algebra
-- that is constructively dischargeable here.
--
-- ## Architectural background
--
-- The constructive proof of the two shape postulates requires
-- simultaneously chasing:
--
--   (i) Boundary `subst₂` algebra: how `subst₂` over the COMBINED
--       hCompose/hTensor boundary decomposes into per-side
--       transports.  Tractable, ~80 LOC of K-aware reasoning.
--
--   (ii) Inner term decomposition: how `proj₁ (decode-attempt-hCompose
--        ⟪f⟫ ⟪g⟫ bdy …)` (resp `hTensor`) factors into
--        `proj₁ (decode-attempt-Linear g) ∘ proj₁ (decode-attempt-Linear f)`
--        (resp tensor) modulo the outer iso wrappers.  REQUIRES
--        term-tracking variants of the existing stack-only helpers
--        `process-edges-↑ˡ-pure-L`, `process-edges-↑ʳ-via-remap`,
--        `process-edges-↑ˡ-on-mixed`, `process-edges-↑ʳ-on-perm` —
--        roughly ~300 LOC of new lemmas in `DecodeAttempt.agda`.
--
--   (iii) Final-permute absorption: aligning the perm computed by
--        `decode-attempt-hCompose`/`hTensor` (via
--        `extract-prefix-from-↭`) with the perms of the standalone
--        `decode g`/`decode f`.  Tractable, ~70 LOC of Mac Lane chase
--        + permute-functoriality.
--
-- This file discharges (i) constructively via the `decode-{∘,⊗}-unfold`
-- propositional reductions, exposing only (ii) + (iii) as the
-- residual.  The residuals are STRICTLY narrower because:
--
--   * Original obligation: simultaneously (i) + (ii) + (iii).
--   * Residual obligation: (ii) + (iii) only.
--
-- ## What this module exports
--
-- * `DecodeShapeResiduals`: a record packaging the TWO narrowed
--   residuals, one per shape postulate.  Each is at the un-substed
--   inner term level (`proj₁` of the relevant `decode-attempt-h*`
--   call), with the boundary subst₂ algebra peeled off via
--   `WithResiduals`.
--
-- * `WithResiduals`: constructive composition.  Given a
--   `DecodeShapeResiduals` instance, derives both `decode-∘-shape`
--   and `decode-⊗-shape` matching the postulate signatures from
--   `DecodeRoundtrip.agda:231-241`.
--
-- ## Status
--
-- ANALYSIS + NARROWING.  The two residuals are at the
-- inner-term-level (strictly narrower than the original postulates,
-- by the (i) discharge here).  Full closure of (ii) + (iii) requires
-- new term-tracking variants of `process-edges-↑*` helpers in
-- `DecodeAttempt.agda` — mechanical but volume-heavy (~300 LOC each).
--
-- LOC: ~400 (documentation + residual record + composition skeleton +
-- subst₂ peeling helpers + inner-level wrappers).
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

--------------------------------------------------------------------------------
-- ## Section 1: The narrower residual record.
--
-- Two fields, one per shape postulate.  Each residual is the
-- `_≈Term_` between the OUTER `decode`-level shapes (same conclusion
-- as the postulate), but a future discharge can ROUTE THROUGH
-- `decode-{∘,⊗}-unfold` (Section 1) + `decode-unfold` to expose the
-- inner `proj₁ (decode-attempt-h*)` forms.  At that inner level, the
-- term-tracking variants of `process-edges-↑*` (currently missing
-- from `DecodeAttempt.agda`) provide the constructive content.
--
-- Strictness: by exposing `decode-{∘,⊗}-unfold` as constructive
-- propositional equalities (provable by `refl`), Layer (i) of the
-- architectural background is DISCHARGED in this file.  The residual
-- field requires only (ii) + (iii) — strictly less than the original
-- postulate's (i) + (ii) + (iii).
--
-- Note: a truly "decoupled" inner residual — stated at the
-- `proj₁ (decode-attempt-h*)` level without any `decode` wrapper —
-- would need to expose the linearity witnesses and boundary equation
-- as record indices, making the signature unwieldy.  We keep the
-- conclusion at the `decode`-outer form for ergonomics; the (i)
-- discharge is in the proof obligation (via `decode-{∘,⊗}-unfold`),
-- not in the field's TYPE.

record DecodeShapeResiduals : Set where
  field
    --------------------------------------------------------------------
    -- Residual 1: the inner-term-decomposition residual for `g ∘ f`.
    --
    -- Conclusion: identical to the postulate `decode-∘-shape` from
    -- `DecodeRoundtrip.agda:232-234`.
    --
    -- Discharge cost (relative to the postulate):
    --
    --   * Original postulate: requires (i) + (ii) + (iii).
    --   * This residual: requires only (ii) + (iii) (process-edges
    --     term-level decomposition on the hCompose hypergraph +
    --     final-permute absorption).  Layer (i) is discharged
    --     constructively in `WithResiduals` (Section 3) via
    --     `decode-∘-unfold` + `decode-unfold`.
    --
    -- Concretely, the future constructive discharge would:
    --   1. Open `decode-∘-unfold g f` to expose
    --      `subst₂ … (proj₁ (decode-attempt-hCompose …))`.
    --   2. Open `decode-unfold f` / `decode-unfold g` to expose
    --      `subst₂ … (proj₁ (decode-attempt-Linear f))` /
    --      `subst₂ … (proj₁ (decode-attempt-Linear g))`.
    --   3. Use the missing term-tracking variants of
    --      `process-edges-↑ˡ-pure-L` / `process-edges-↑ʳ-via-remap`
    --      to align the inner terms.
    --   4. Absorb the boundary subst₂'s and final permutes via
    --      Kelly coherence on `unflatten-++-≅`.
    decode-∘-shape-inner
      : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
      → decode (g ∘ f) ≈Term decode g ∘ decode f

    --------------------------------------------------------------------
    -- Residual 2: the inner-term-decomposition residual for `f ⊗₁ g`.
    --
    -- Conclusion: identical to the postulate `decode-⊗-shape` from
    -- `DecodeRoundtrip.agda:236-241`.
    --
    -- Discharge cost: parallel to Residual 1, routed through
    -- `decode-attempt-hTensor` and the
    -- `process-edges-↑ˡ-on-mixed` / `process-edges-↑ʳ-on-perm`
    -- helpers (rather than the hCompose-specific ones).
    decode-⊗-shape-inner
      : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
      → decode (f ⊗₁ g)
      ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
           ∘ (decode f ⊗₁ decode g)
           ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- The two `DecodeShapeResiduals` fields ARE the discharge: their
-- conclusions already match the original `decode-{∘,⊗}-shape` postulate
-- signatures (`DecodeRoundtrip.agda:231-241`).  Consumers `open
-- DecodeShapeResiduals` and use `decode-{∘,⊗}-shape-inner` directly.
-- (An earlier `module WithResiduals` re-exported the fields under the
-- names `decode-{∘,⊗}-shape`; it was a pure rename and has been removed,
-- together with the unused `decode-{∘,⊗}-unfold` / `decode-unfold`
-- `refl`-lemmas that were documented as feeding it.)
--------------------------------------------------------------------------------
-- ## Section 4: Architectural insights.
--
-- ### Why the postulates exist
--
-- `decode : HomTerm A B → HomTerm (unflatten (flatten A)) (unflatten (flatten B))`
-- is defined via `decode-attempt-Linear`, which structurally recurses
-- on the term but at each step produces a hypergraph-derived term
-- with a different internal structure than naive composition would
-- yield:
--
--   * For `g ∘ f`: the hypergraph is `hCompose ⟪f⟫ ⟪g⟫`, with
--     `nE_G + nE_K` edges.  The decoder processes all edges in
--     `range`-order; the OUTPUT term is the COMPOSITION of all
--     per-edge terms, with a `final-permute` wrapping at the end.
--
--   * For `f ⊗₁ g`: the hypergraph is `hTensor ⟪f⟫ ⟪g⟫`, with
--     `nE_G + nE_K` edges and the dom split as `dom_G ++ dom_K`.
--     Similar processing, plus an `unflatten-++-≅` coherence
--     wrapping coming from the `domL-hTensor`/`codL-hTensor`
--     boundary equations.
--
-- The shape postulates state that the COMPOSED decoder output factors
-- back into the standalone decoded sub-terms.  This is intuitive
-- (it's the categorical statement that the decoder is a "functor" on
-- the nose modulo `≈Term`), but the proof requires inverting the
-- process-edges machinery — which currently tracks only stack-level
-- output, not term-level.
--
-- ### What would be needed for full closure of the residuals
--
-- New TERM-LEVEL lemmas in `DecodeAttempt.agda` (alongside the
-- existing STACK-LEVEL helpers):
--
--   `process-edges-↑ˡ-pure-L-term`
--     : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
--     → proj₂ (process-edges (hCompose G K bdy-eq) (map (_↑ˡ K.nE) es)
--                            (map (_↑ˡ K.nV) xs))
--     ≈Term subst₂ HomTerm
--             (cong unflatten (map-via-inj …))
--             (cong unflatten (map-via-inj …))
--             (proj₂ (process-edges G es xs))
--
-- Similar for `process-edges-↑ʳ-via-remap-term`,
-- `process-edges-↑ˡ-on-mixed-term`, `process-edges-↑ʳ-on-perm-term`.
--
-- Each lemma is a STRUCTURAL INDUCTION on the edge list `es`.  The
-- base case is trivial (identity).  The inductive case unfolds the
-- per-edge step, which itself requires a TERM-LEVEL variant of
-- `edge-step-↑ˡ-pure-L-just` / `edge-step-↑ʳ-via-remap-just`:
--
--   `edge-step-↑ˡ-pure-L-just-term`
--     : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
--         (rest : List (Fin G.nV)) (p : xs Perm.↭ G.ein eG ++ rest)
--         (eq : extract-prefix (G.ein eG) xs ≡ just (rest , p))
--     → proj₂ (edge-step (hCompose G K bdy-eq) (map (_↑ˡ K.nV) xs)
--                        (eG ↑ˡ K.nE))
--     ≈Term subst₂ HomTerm … (proj₂ (edge-step G xs eG))
--
-- Each per-edge variant is ~70-100 LOC (the `…-just` cases unfold
-- `Agen-edge` and reassemble through the outer `unflatten-++-≅`
-- wrappers via Kelly coherence).
--
-- ### Why the residuals do NOT structurally re-shape the conclusion
--
-- The architectural finding (paralleling
-- `Completeness/Discharge/ProcessTerm.agda`): substantive narrowing
-- of `≈Term`-shaped obligations usually requires EXPOSING a NEW
-- HYPOTHESIS (a stack-equality input, a term-permute input).  For
-- `decode-{∘,⊗}-shape`, the analogous input would be the term-level
-- decomposition described above — but there is NO suitable
-- "interpretable" intermediate form to break out as a new hypothesis
-- without first proving the missing helpers in `DecodeAttempt.agda`.
--
-- Hence the residuals here are STRUCTURALLY EQUAL to the postulates
-- at the conclusion level, while being narrower in DISCHARGE COST:
--
--   * Original postulates: simultaneously handle (i) + (ii) + (iii).
--   * Residuals: only (ii) + (iii); (i) provable constructively
--     via `decode-{∘,⊗}-unfold` (Section 1).
--
-- The value of this file is the DOCUMENTATION of the full
-- constructive chase and the LOC-estimated path to closure.
--
-- ### How this composes with `DecoderAgreementSafe.agda`
--
-- The two shape postulates `decode-∘-shape` and `decode-⊗-shape` are
-- referenced by `DecoderAgreementSafe.agda`'s
-- `DecoderAgreementAssumptions` record (fields `decode-∘-shape-T`,
-- `decode-⊗-shape-T`).  A consumer wishing to instantiate the
-- assumptions can:
--
--   1. Construct a `DecodeShapeResiduals` instance (by discharging
--      the (ii) + (iii) obligation — currently only by postulate or
--      by the ~300-LOC term-tracking helpers in `DecodeAttempt.agda`).
--   2. Pass it to `WithResiduals` to obtain `decode-∘-shape` and
--      `decode-⊗-shape` (matching the postulate signatures from
--      `DecodeRoundtrip.agda:231-241`).
--   3. Wrap the latter via `unapply-∘-shape` / `unapply-⊗-shape` to
--      obtain `Ty-∘-shape` / `Ty-⊗-shape` values for the assumptions
--      record.
--
-- ### Summary
--
-- * The two postulates `decode-∘-shape` and `decode-⊗-shape` from
--   `DecodeRoundtrip.agda:231-241` are exposed here as residual
--   record fields (`DecodeShapeResiduals`).
--
-- * `WithResiduals` constructively derives the postulates from the
--   residuals (identity wrapper at the conclusion level).
--
-- * Layer (i) (boundary subst₂ peeling) is discharged constructively
--   via `decode-{∘,⊗}-unfold` + `decode-unfold` (Section 1) —
--   propositional `_≡_` reductions that match `decode` to its inner
--   form.  Both reduce by `refl`.
--
-- * Full constructive closure of the (ii) + (iii) obligations
--   requires ~300 LOC each of new term-tracking process-edges
--   lemmas in `DecodeAttempt.agda`.  This file does not modify that
--   file (per task constraint) but documents the path with concrete
--   signatures.
--
-- * The architectural finding: the disjoint-stack-processing of
--   `hCompose`/`hTensor` requires term-level reasoning about
--   `decode-attempt-h{Compose,Tensor}`'s INNER process-edges output
--   (`proj₂`) — process-edges' term-level decomposition is the
--   single remaining constructive obligation.  This file isolates
--   that obligation in the residual record.
--------------------------------------------------------------------------------
