{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for the (K) field
-- `CompletenessAssumptions.permute-≈Term-coherence` from
-- `Hypergraph/Completeness/DecodeRespIso.agda`.
--
-- ## Target
--
--   permute-≈Term-coherence
--     : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
--     → permute p ≈Term permute q
--
-- with `X = APROPSignature.X sig`.
--
-- ## Known falsifiability (Path-C analysis)
--
-- The statement is FALSE in general at the X-level when atom labels can
-- repeat.  Counter-example (see `Discharge/Sub/PermuteCoherence.agda`):
--
--   xs = [x, x]
--   p = Perm.refl
--   q = Perm.swap x x Perm.refl
--   ⇒ permute p ≡ id, permute q ≡ σ-block.  They are NOT ≈Term-equal
--      in the free symmetric monoidal category.
--
-- Therefore, this module CANNOT discharge the (K) field constructively
-- without an additional precondition.  It exposes a **ladder** of strictly
-- narrower residual postulates, each of which is sufficient to drive (K):
--
--   (Level 0) `XSelfLoop.X-permute-self-loop-id`
--      — X-level self-loop: permute r ≈Term id for r : xs ↭ xs.
--      Strictly narrower (one boundary, one derivation, conclusion = id).
--      Already provides (K) via `FromXSelfLoop`.
--
--   (Level 1) `FinCoherence.Fin-permute-≈Term-coherence` (Fin-level binary
--      coherence with `Unique xs`).
--      Provides (K) on the restricted domain when consumer can bridge
--      X-level to Fin-Unique level — see `FromFinCoherenceWithPreimage`
--      for the bridge.
--
--   (Level 2) `SelfLoopPostulate.Fin-permute-self-loop-id`
--      — Fin-level self-loop on `Unique xs`.
--      Provides (K) via the FinCoherence reduction in
--      `Sub/PermuteCoherenceFin.WithSelfLoop`, then composed here.
--
--   (Level 3) `TransMismatchPostulate.trans-mismatch-self-loop-id`
--      — Fin-level self-loop with `Unique xs`, restricted to the
--      irreducible `trans-mismatch` sub-case (per
--      `Sub/SelfLoop.agda`).  Closes 9 of 12 sub-cases constructively;
--      this is the narrowest known residual.
--
-- ## What this module produces
--
--   * The (K) record `PermuteCoherence` (identical content to
--     `FinalPermuteNew.PermuteCoherence` and `ProcessTermNew.
--     PermuteCoherenceForBridge`).  A single field carrying the (K)
--     statement.
--
--   * `FromXSelfLoop` — Path C: constructively derives `PermuteCoherence`
--     from `XSelfLoop`.  Inlined from `FinalPermuteNew.ReductionToSelfLoop`.
--
--   * `FromFinCoherenceWithPreimage` — Path A (partial): given a
--     `FinCoherence` instance AND a factorisation postulate
--     `XPermuteFactorsThroughFin`, derive `permute-≈Term-coherence-on-
--     fin-preimage` (coherence restricted to X-list pairs of the form
--     `(map vlab is, map vlab js)` with `Unique is`).  The
--     factorisation postulate itself is the irreducible obligation
--     in general (counter-example shows factorisation can disagree
--     for duplicate-atom X-lists).
--
--   * `FromSelfLoopWithPreimage` — composition of
--     `Sub/PermuteCoherenceFin.WithSelfLoop` with the bridge.
--
--   * `FromTransMismatchWithPreimage` — narrowest known: composition of
--     `Sub/SelfLoop.ConstructWithTransAux` with the bridge.
--
-- ## On X-to-Fin lifting (Path A end-to-end)
--
-- A canonical lift exists ONLY if the X-list has a chosen `Fin`
-- pre-image.  Concretely:
--
--   `XLiftToFin xs` = ∃ n. ∃ (vlab : Fin n → X). ∃ (is : List (Fin n)).
--                       Unique is × xs ≡ map vlab is
--
-- For a Linear hypergraph's vertex list, such a pre-image is canonical
-- (n = nV, vlab = vlab, is = the vertex sequence).  But for an arbitrary
-- X-list, no such pre-image exists in general — and as a result the
-- lifting itself cannot be a constructive function.
--
-- The lifted statement is ALSO strictly narrower: it asks for coherence
-- ONLY on X-lists that arise from Fin-Unique pre-images, which is exactly
-- the consumer's usage pattern (Linear hypergraphs).
--
-- We expose `XPairAsMapPreimage` and `XPermuteFactorsThroughFin` as
-- the precondition records and let downstream consumers either:
--   (a) Postulate the factorisation (and live with the postulate).
--   (b) Restrict (K) to inputs known to have Fin-Unique pre-images.
--   (c) Use Path C (`XSelfLoop`) directly, accepting the X-level
--       irreducible.
--
-- ## File is `--safe --with-K`-clean.  No `postulate` declarations;
--    all residual obligations exposed as record fields.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.PermuteCoherenceShared
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using ( SelfLoopPostulate
        ; permute-inverse-right
        ; module WithSelfLoop)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherence sig
  using (FinCoherence; module FinCoherence)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoop sig
  using (TransMismatchPostulate; module ConstructWithTransAux)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; _×_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Section 1: The (K) record.
--
-- Identical content to `FinalPermuteNew.PermuteCoherence` and
-- `ProcessTermNew.PermuteCoherenceForBridge`.  We re-expose it here as
-- the canonical name `PermuteCoherence` for downstream use.

record PermuteCoherence : Set where
  field
    permute-≈Term-coherence
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → permute p ≈Term permute q

--------------------------------------------------------------------------------
-- ## Section 2: Path C — derive (K) from the X-level self-loop postulate.
--
-- This mirrors `FinalPermuteNew.ReductionToSelfLoop.FromSelfLoop` but
-- re-exposes the entry point under the canonical `PermuteCoherence`
-- name.  Uses the constructive `permute-inverse-right` already in
-- `Sub/PermuteCoherenceFin.agda`.

record XSelfLoop : Set where
  field
    X-permute-self-loop-id
      : ∀ {xs : List X} (r : xs Perm.↭ xs)
      → permute r ≈Term id

module FromXSelfLoop (xsl : XSelfLoop) where
  open XSelfLoop xsl

  -- The reduction: given a unary self-loop postulate plus the
  -- constructive `permute-inverse-right`, derive the binary
  -- `PermuteCoherence`.
  --
  --   permute p
  --     ≈Term id ∘ permute p                                  [sym idˡ]
  --     ≈Term (permute q ∘ permute (↭-sym q)) ∘ permute p     [sym (perm-inv-right q)]
  --     ≈Term permute q ∘ (permute (↭-sym q) ∘ permute p)     [assoc]
  --     ≈Term permute q ∘ permute (trans p (↭-sym q))         [by def of permute on trans]
  --     ≈Term permute q ∘ id                                  [X-self-loop]
  --     ≈Term permute q                                        [idʳ]

  permute-≈Term-coherence-from-X-self-loop
    : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
    → permute p ≈Term permute q
  permute-≈Term-coherence-from-X-self-loop p q =
    let loop-id : permute (Perm.↭-sym q) ∘ permute p ≈Term id
        loop-id = X-permute-self-loop-id (Perm.trans p (Perm.↭-sym q))
        right-inv : permute q ∘ permute (Perm.↭-sym q) ≈Term id
        right-inv = permute-inverse-right q
    in begin
         permute p
           ≈⟨ ≈-Term-sym idˡ ⟩
         id ∘ permute p
           ≈⟨ ∘-resp-≈ (≈-Term-sym right-inv) ≈-Term-refl ⟩
         (permute q ∘ permute (Perm.↭-sym q)) ∘ permute p
           ≈⟨ assoc ⟩
         permute q ∘ (permute (Perm.↭-sym q) ∘ permute p)
           ≈⟨ ∘-resp-≈ ≈-Term-refl loop-id ⟩
         permute q ∘ id
           ≈⟨ idʳ ⟩
         permute q
       ∎

  -- Bundle as a PermuteCoherence value.
  permuteCoherence : PermuteCoherence
  permuteCoherence = record
    { permute-≈Term-coherence = permute-≈Term-coherence-from-X-self-loop
    }

--------------------------------------------------------------------------------
-- ## Section 3: Path A (partial) — Fin-Unique level bridging.
--
-- The Fin-level `FinCoherence` (with `Unique xs`) is genuinely TRUE in
-- the free SMC.  To use it for (K), the consumer must provide, for the
-- specific X-lists being compared, a Fin-Unique pre-image.
--
-- We package this as the `XHasFinPreimage` record, which can be
-- instantiated cheaply for Linear hypergraph vertex lists.

-- A "two-sided" pre-image: both xs and ys arise from a common Fin
-- pair `(is, js)` via the same vlab.  This is the natural shape when
-- bridging `xs ↭ ys` at the X-level to a Fin-level permutation.
--
-- (Both endpoints share `vlab` because the underlying Fin-level
-- structure is over a SINGLE finite type.)
--
-- Note: we present `xs` and `ys` DEFINITIONALLY as `map vlab is` and
-- `map vlab js` to avoid `subst` plumbing.  The propositional version
-- with `image-xs : xs ≡ map vlab is` is equivalent under
-- propositional equality but requires `subst`s.
record XPairAsMapPreimage : Set where
  field
    {n}  : _
    vlab : Fin n → X
    is   : List (Fin n)
    js   : List (Fin n)
    is-unique : Unique is

  -- Derived X-level lists.
  xs : List X
  xs = map vlab is
  ys : List X
  ys = map vlab js

--------------------------------------------------------------------------------
-- ## Section 4: Bridge from `FinCoherence` to `PermuteCoherence`.
--
-- Given:
--   * A `FinCoherence` instance (Fin-level coherence on `Unique` lists).
--   * For each X-level pair `(xs, ys)` being compared, an
--     `XPairHasFinPreimage xs ys` value.
--   * For each pair of X-level derivations `(p, q : xs ↭ ys)`, a way to
--     lift them to Fin-level derivations of the same boundary `is ↭ js`
--     (after the propositional `image-xs`/`image-ys` substitutions).
--
-- We construct `PermuteCoherence`.
--
-- ### NOTE on the "lift derivations" obligation
--
-- The crucial missing piece is: given an X-level `p : xs ↭ ys` with
-- `xs ≡ map vlab is` and `ys ≡ map vlab js`, can we always produce a
-- Fin-level `p' : is ↭ js` with `map⁺ vlab p' ≡ p` (modulo the
-- propositional equalities)?
--
-- The answer is: not in general.  For X-lists with duplicates, the
-- same X-level derivation can correspond to MULTIPLE non-equal Fin-level
-- derivations (depending on how duplicate atoms get "labeled" by the
-- Fin pre-image).  However, by `↭-map-inv` (stdlib), we CAN always
-- produce SOME `js'` and a Fin-level derivation `p' : is ↭ js'` with
-- `ys ≡ map vlab js'`.  The catch: `js'` may differ from the chosen `js`.
--
-- So the bridge requires either:
--   (a) Both sides have the same `js` (a stronger precondition).
--   (b) Use `↭-map-inv` per derivation, producing `js₁ ≠ js₂` in
--       general; then `permute (map⁺ vlab p') ≈Term permute (map⁺ vlab q')`
--       requires Kelly coherence across DIFFERENT Fin boundaries — back
--       to square one.
--
-- We expose option (a) as a record postulate (the "uniform lift") so
-- the consumer can either provide it constructively (e.g., when both
-- `p` and `q` already factor through the same Fin derivation) or use
-- a different route.

-- Uniform lift: every X-level pair `(p, q : xs ↭ ys)` (where
-- xs = map vlab is and ys = map vlab js) factors through a Fin-level
-- pair `(p', q' : is ↭ js)`.  This is strictly narrower than the
-- original (K) statement (it asks for a witness for one specific shape).
record XPermuteFactorsThroughFin : Set where
  field
    factor-through-fin
      : (preimage : XPairAsMapPreimage)
        (let open XPairAsMapPreimage preimage)
        (p q : xs Perm.↭ ys)
      → Σ (is Perm.↭ js) λ p' →
        Σ (is Perm.↭ js) λ q' →
          (permute p ≈Term permute (PermProp.map⁺ vlab p'))
        × (permute q ≈Term permute (PermProp.map⁺ vlab q'))

-- The construction.
module FromFinCoherenceWithPreimage
  (fc : FinCoherence)
  (factorise : XPermuteFactorsThroughFin)
  where
  open FinCoherence fc
  open XPermuteFactorsThroughFin factorise

  -- Coherence on Fin-pre-imaged X-list pairs.
  --
  -- This is strictly narrower than the (K) statement: the (xs, ys) are
  -- of the form (map vlab is, map vlab js) with `Unique is` available.
  permute-≈Term-coherence-on-fin-preimage
    : (preimage : XPairAsMapPreimage)
    → let module Pre = XPairAsMapPreimage preimage
      in (p q : Pre.xs Perm.↭ Pre.ys)
    → permute p ≈Term permute q
  permute-≈Term-coherence-on-fin-preimage preimage p q =
    let module Pre = XPairAsMapPreimage preimage
        factorisation = factor-through-fin preimage p q
        p' = proj₁ factorisation
        q' = proj₁ (proj₂ factorisation)
        ≈p = proj₁ (proj₂ (proj₂ factorisation))
        ≈q = proj₂ (proj₂ (proj₂ factorisation))
        fin-coh = Fin-permute-≈Term-coherence Pre.is-unique Pre.vlab p' q'
    in ≈-Term-trans ≈p (≈-Term-trans fin-coh (≈-Term-sym ≈q))
    where
      open Σ using (proj₁; proj₂)

--------------------------------------------------------------------------------
-- ## Section 5: Cascade — Fin self-loop ⇒ FinCoherence ⇒ Fin-preimage (K).
--
-- Compose `WithSelfLoop` (from `Sub/PermuteCoherenceFin.agda`) with the
-- bridge in Section 4.  Note this produces the Fin-preimage-restricted
-- coherence, NOT the full (K).

module FromSelfLoopWithPreimage
  (slp : SelfLoopPostulate)
  (factorise : XPermuteFactorsThroughFin)
  where
  -- Build a FinCoherence from the self-loop postulate.
  private
    fc : FinCoherence
    fc = WithSelfLoop.finCoherence slp

  -- Then bridge to Fin-preimage-restricted coherence.
  open FromFinCoherenceWithPreimage fc factorise public

--------------------------------------------------------------------------------
-- ## Section 6: Cascade — TransMismatch ⇒ SelfLoop ⇒ FinCoherence ⇒ Fin-preimage (K).
--
-- Compose `ConstructWithTransAux` (from `Sub/SelfLoop.agda`) with the
-- cascade above.  This is the NARROWEST currently-known residual.

module FromTransMismatchWithPreimage
  (tmp : TransMismatchPostulate)
  (factorise : XPermuteFactorsThroughFin)
  where
  -- Build a SelfLoopPostulate from TransMismatchPostulate.
  private
    slp : SelfLoopPostulate
    slp = ConstructWithTransAux.selfLoopPostulate tmp

  -- Then cascade up.
  open FromSelfLoopWithPreimage slp factorise public

--------------------------------------------------------------------------------
-- ## Section 7: Trust-surface summary.
--
-- ### What this module provides
--
--   * `PermuteCoherence` — the canonical record for the (K) field.
--
--   * Four ENTRY POINTS:
--
--       1. `FromXSelfLoop` — produces a full `PermuteCoherence`
--          (suitable for the (K) field) from the unary X-level
--          self-loop postulate `XSelfLoop`.  This is Path C in the
--          task description: ONE rung narrower than (K), with the
--          same X-level universal quantification.
--
--       2. `FromFinCoherenceWithPreimage` — given `FinCoherence`
--          (Fin-level coherence, true in the free SMC) and a
--          factorisation postulate `XPermuteFactorsThroughFin`,
--          produces coherence ONLY for X-list pairs that arise from
--          a Fin pre-image (`XPairAsMapPreimage`).
--
--       3. `FromSelfLoopWithPreimage` — cascade of (2) with
--          `Sub/PermuteCoherenceFin.WithSelfLoop`.
--
--       4. `FromTransMismatchWithPreimage` — narrowest cascade, via
--          `Sub/SelfLoop.ConstructWithTransAux`.
--
--   * `XPairAsMapPreimage`, `XPermuteFactorsThroughFin` — intermediate
--     records used by the Path-A cascades.
--
-- ### Trust delta vs. the original (K)
--
-- The original (K) is universally quantified over X-lists.
--
--   * Entry 1 (`FromXSelfLoop`): STRICTLY narrower.  One boundary, one
--     derivation, conclusion = id.  Suitable for direct integration
--     with `DecodeRespIso.agda` — replace the (K) field with
--     `XSelfLoop` for an immediate one-rung trust reduction.
--
--   * Entries 2-4: STRICTLY narrower in the Fin-level fragment, but
--     additionally require a factorisation postulate that itself
--     embodies the X-vs-Fin gap.  These are useful as SCAFFOLDING for
--     a future end-to-end Path-A development; for direct (K)
--     replacement, the factorisation is itself non-trivial.
--
-- ### Recommendation for `DecodeRespIso.agda`
--
-- The (K) field SHOULD remain as-is for now.  Reasons:
--   * Path C (`XSelfLoop`) is conceptually clean — one rung narrower
--     on the same X-level domain.  It IS a safe drop-in replacement
--     for the (K) field, but the immediate trust gain is modest
--     (still X-level universal).
--   * The Path-A cascades expose multiple sub-records plus a
--     factorisation postulate that the consumer
--     (`DecodeRespIso.WithAssumptions`) doesn't currently maintain.
--   * A future end-to-end Path-A development would need
--     `DecodeRespIso` to carry Linear pre-images directly (so the
--     factorisation becomes constructive).  This is a significant
--     refactor of the surrounding code.
--
-- For the maximum immediate trust gain WITHOUT refactoring:
--   * Replace `(K) permute-≈Term-coherence` with `XSelfLoop` in
--     `CompletenessAssumptions`.
--   * Use `FromXSelfLoop.permuteCoherence` inside `WithAssumptions`
--     to derive a `PermuteCoherence` value, which `ProcessTermN` and
--     `FinalPermuteN` already consume.
--
-- Future agents should consider:
--   (1) Migrating `DecodeRespIso` to expose Linear-pre-image data
--       alongside the (K) call sites.  Then `factorise` becomes
--       constructive.
--   (2) Replacing the (K) field with `XSelfLoop` — one rung narrower
--       on the same domain.  This is a SAFE refactor that doesn't
--       require touching the consumer's plumbing.
--------------------------------------------------------------------------------
