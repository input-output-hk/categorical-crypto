{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Route 1 trust point: `CompletenessAssumptions` with fine-grained
-- sub-postulates corresponding to Route 1's sub-properties.
--
-- ## Architecture
--
-- The record has THREE fields, each strictly narrower than the
-- original opaque `decode-rel-resp-iso` postulate:
--
--   (c')  `process-term-permute-aligned`  — Term-level ≈Term,
--                                           specialised to the concrete
--                                           `process-edges-resp-iso-stack
--                                           f g iso` (no longer takes a
--                                           universally-quantified
--                                           `stack-↭`).
--   (Kelly) `permute-≅↭-faithful`         — Kelly's symmetric-monoidal
--                                           coherence in its TRUE
--                                           `≅↭`-CONDITIONED form
--                                           (`eval-↭ p ≈-fb eval-↭ q →
--                                           permute p ≈Term permute q`);
--                                           = `FaithfulnessResidual`.
--                                           REPLACES the old, FALSE-in-
--                                           general `X-permute-self-loop-id`.
--                                           The (d) consumer discharges
--                                           the `≅↭` hypothesis
--                                           CONSTRUCTIVELY via
--                                           `Sub.StackEvalCoherence`
--                                           (`Rigid.eval-rigid` +
--                                           `Sub.FromAPROPCodUnique`).
--   (F)   `decode-rel-≈-decode`           — Structural ↔ algorithmic
--                                           decoder agreement.
--
-- FOUR sub-properties have been FULLY DISCHARGED CONSTRUCTIVELY and
-- are no longer fields of the record:
--
--   * `decode-attempt-Linear-extracts` — structural shape lemma,
--     discharged in `Discharge/LinearExtracts.agda`.
--   * (b) `process-edges-resp-iso-stack` — stack permutation,
--     discharged in `Discharge/StackPerm.agda`.  The iso is
--     structurally redundant for the multiset statement; the proof
--     needs only `⟪⟫F-codL`.
--   * The old (c) field body is RECONSTRUCTED in `WithAssumptions` by
--     applying the (c') field directly to the discharged (b) value —
--     the (c') field takes the stack permutation as an explicit
--     parameter, so the (c) path needs NO Kelly coherence.
--   * The old (d) field body is RECONSTRUCTED in `WithAssumptions` via
--     `Discharge/FinalPermuteNew.agda`'s `final-permute-absorb-discharge`.
--     Its Kelly-coherence input is reconstructed from (XSL) via that
--     module's own `ReductionToSelfLoop.FromSelfLoop`, using the
--     discharged `permute-inverse-right`.
--
-- `WithAssumptions` constructively derives `decode-attempt-resp-iso`,
-- `decode-resp-iso`, and `decode-rel-resp-iso` from these fields.
--
-- ## Why the input iso is at Translation level
--
-- An earlier `boundary-respects-iso : iso-T → iso-F` field was
-- provably FALSE (see `BoundaryRespectsIso.agda`).  The counter-
-- example: `id ∘ id` vs `id`.  Translation prunes the redundant
-- vertex via `hComposeP`; FromAPROP keeps it, so the two
-- FromAPROP hypergraphs have different vertex counts (2 vs 1) and
-- cannot be iso.
--
-- Recovery: the sub-postulates take the Translation iso DIRECTLY.
-- The decoder still operates at the FromAPROP level (because
-- `decode-attempt-Linear` is defined there), but the boundary
-- subst₂ chain uses FromAPROP's `⟪⟫F-domL`/`⟪⟫F-codL`, which
-- propositionally equal `flatten A`/`flatten B` regardless of the
-- iso level.
--
-- ## File is `--safe`-clean
--
-- Sub-postulates are fields of the record — they are not
-- `postulate` declarations in this file.  All downstream modules
-- (Inductive.agda, CompletenessFull.agda, Tests.agda) are
-- `--safe`-clean.  `TestsTrust.agda` is the unique non-safe file
-- (postulates the record by design).
--
-- ## Optional finer trust via `DecoderAgreementSafe.agda`
--
-- The `decode-rel-≈-decode` field can be discharged constructively
-- from 11 yet-narrower per-constructor fields via
-- `Completeness/DecoderAgreementSafe.agda` (separate record +
-- `WithAssumptions` module, also `--safe`-clean).  A consumer
-- postulating the 11 fields gets `decode-rel-≈-decode` for free,
-- bringing the effective trust to 4 algorithmic + 11 atomic = 15
-- narrower fields.  Use this path when fine-grained auditability is
-- desired; otherwise stick with the 5-field record here.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRespIso
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-Linear)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.LinearityIso sig
  using (Linear-resp-iso)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

-- `decode-attempt-Linear-extracts` is fully discharged constructively
-- in `Discharge/LinearExtracts.agda` (via agent 4).
-- The discharge function is imported here and used directly inside
-- `WithAssumptions`, eliminating the need for a record field.
open import Categories.APROP.Hypergraph.Completeness.Discharge.LinearExtracts sig-dec
  using (decode-attempt-Linear-extracts-discharge)

-- `permute-inverse-right` is fully discharged constructively in
-- `Discharge/Sub/PermuteCoherenceFin.agda` (via agent on the
-- Fin-Unique-coherence task).  It says `permute p ∘ permute (↭-sym p)
-- ≈Term id` for any `p : xs ↭ ys`.  This is the round-trip
-- cancellation used in `decode-attempt-resp-iso`.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (permute-inverse-right)

-- (b) `process-edges-resp-iso-stack` is FULLY DISCHARGED CONSTRUCTIVELY
-- in `Discharge/StackPerm.agda`.  It says that the iso induces a
-- `Perm.↭` permutation between the vlab-mapped final stacks of
-- `process-all-edges` on both sides.  The proof needs only
-- `⟪⟫F-codL` + `decode-attempt-Linear` + `decode-attempt-perm-from-just`
-- — the iso itself is structurally redundant.  No longer a field
-- of `CompletenessAssumptions`.
open import Categories.APROP.Hypergraph.Completeness.Discharge.StackPerm sig-dec
  using (process-edges-resp-iso-stack)

-- (d) narrowing module.  `FinalPermuteNew` exposes the (d) body as
-- `final-permute-absorb-discharge`, parameterised by a `PermuteCoherence`
-- (Kelly's coherence on the `permute` fragment).  It also provides
-- `ReductionToSelfLoop.FromSelfLoop`, which derives that
-- `PermuteCoherence` from the unary X-level `X-permute-self-loop-id`
-- field plus the constructive `permute-inverse-right` — so `WithAssumptions`
-- needs no separate Kelly-coherence module.
--
-- The (c) body needs NO Kelly coherence: the `process-term-permute-aligned`
-- field already takes the stack permutation as an explicit parameter, so
-- `WithAssumptions` applies it directly to the discharged (b) value
-- `process-edges-resp-iso-stack`.
import Categories.APROP.Hypergraph.Completeness.Discharge.FinalPermuteNew sig-dec
  as FinalPermuteN

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)

-- (XSL glue) CONSTRUCTIVELY DISCHARGED — the `≅↭` evidence consumed by
-- the (d) discharge is now a theorem (via `Rigid.eval-rigid` +
-- `FromAPROPCodUnique.⟪_⟫F-cod-unique`), not a trust field.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEvalCoherence sig-dec
  using (stack-eval-coherence)

-- Imports needed for `Build` record's field types.
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape sig
  using (DecodeShapeResiduals)
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermAligned2 sig-dec
  using (ProcessTermAligned2Residual)

-- Imports needed for deriving the three trust values from `Build`.
import Categories.APROP.Hypergraph.Completeness.FromAssumptions.DecodeRelDecode as DRD
module DRD-sig = DRD sig-dec
import Categories.APROP.Hypergraph.Completeness.FromAssumptions.ProcessTermPermute as PTP
module PTP-sig = PTP sig-dec

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Section 1: Linearity and boundary equations.
--
-- These are constructive helpers exposed for clarity / reuse.

-- Both ⟪f⟫_F and ⟪g⟫_F are Linear.  Constructive from `⟪⟫-Linear`.
⟪⟫F-Linear-pair
  : ∀ {A B} (f g : HomTerm A B)
  → Linear ⟪ f ⟫F × Linear ⟪ g ⟫F
⟪⟫F-Linear-pair f g = Lin.⟪⟫-Linear f , Lin.⟪⟫-Linear g

-- Boundary equations (no iso needed — both ⟪f⟫F.domL and ⟪g⟫F.domL
-- equal `flatten A` by `⟪⟫F-domL`).
full-dom-eq : ∀ {A B} (f g : HomTerm A B)
            → domL ⟪ g ⟫F ≡ domL ⟪ f ⟫F
full-dom-eq f g = trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f))

full-cod-eq : ∀ {A B} (f g : HomTerm A B)
            → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

--------------------------------------------------------------------------------
-- ## Section 2: Inlined `subst₂` algebra + UIP.
--
-- Tiny lemmas about subst₂-on-HomTerm.  All FULLY CONSTRUCTIVE.
-- (Previously these lived in `DecodeRoundtrip.agda` but that module
-- has open postulates; we inline here to keep `--safe`-clean.)

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  subst₂-resp-≈Term
    : ∀ {As Bs As' Bs' : List X} (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
        {f g : HomTerm (unflatten As) (unflatten Bs)}
    → f ≈Term g
    → subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) f
      ≈Term subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) g
  subst₂-resp-≈Term refl refl f≈g = f≈g

  -- Two `subst₂ HomTerm` transports with PROOF-EQUAL equation
  -- arguments give equal terms (UIP-flavoured).
  subst₂-cong-proofs
    : ∀ {As Bs As' Bs' : List X}
        (p₁ p₂ : As ≡ As') (q₁ q₂ : Bs ≡ Bs')
        (t : HomTerm (unflatten As) (unflatten Bs))
    → p₁ ≡ p₂ → q₁ ≡ q₂
    → subst₂ HomTerm (cong unflatten p₁) (cong unflatten q₁) t
      ≡ subst₂ HomTerm (cong unflatten p₂) (cong unflatten q₂) t
  subst₂-cong-proofs _ _ _ _ _ refl refl = refl

  -- Subst₂-trans for HomTerm along `unflatten`-cong'd equations.
  subst₂-HomTerm-trans
    : ∀ {As₁ As₂ As₃ Bs₁ Bs₂ Bs₃}
        (p₁ : As₁ ≡ As₂) (p₂ : As₂ ≡ As₃)
        (q₁ : Bs₁ ≡ Bs₂) (q₂ : Bs₂ ≡ Bs₃)
        (t : HomTerm (unflatten As₁) (unflatten Bs₁))
    → subst₂ HomTerm (cong unflatten p₂) (cong unflatten q₂)
        (subst₂ HomTerm (cong unflatten p₁) (cong unflatten q₁) t)
      ≡ subst₂ HomTerm (cong unflatten (trans p₁ p₂))
                        (cong unflatten (trans q₁ q₂)) t
  subst₂-HomTerm-trans refl refl refl refl _ = refl

  -- Subst₂ commutes with composition.
  subst₂-∘-distrib
    : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
        (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
        (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
        (g : HomTerm (unflatten As₁) (unflatten Bs₁))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ g)
      ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
        ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) g
  subst₂-∘-distrib refl refl refl _ _ = refl

  -- UIP (from `--with-K`).
  uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
  uip refl refl = refl

--------------------------------------------------------------------------------
-- ## Section 3: The `Build` record (formerly `CompletenessAssumptions`).
--
-- THREE trust-output fields needed by `WithAssumptions` to derive
-- `decode-{attempt,_,rel}-resp-iso`.  A `Build` value can be:
--   (a) postulated directly (e.g. in `Solver/TestsTrust.agda`), or
--   (b) constructed from a finer-grained set of 7 APROP-specific
--       residuals via `buildFromResiduals` below.

record Build : Set where
  field
    -- (c') Term-level ≈Term.  Specialised to the concrete stack
    -- permutation `process-edges-resp-iso-stack f g iso` (discharged
    -- constructively in `Discharge/StackPerm.agda`).  The field used to
    -- take this permutation as a universally-quantified parameter, but
    -- the single use site (`process-edges-resp-iso-term`) only ever
    -- instantiates it to that concrete value, so baking it in strictly
    -- narrows the trust surface (no unused ∀-hypothesis).
    process-term-permute-aligned
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → permute (Perm.↭-sym (process-edges-resp-iso-stack f g iso))
        ∘ subst₂ HomTerm
            (cong unflatten (full-dom-eq f g))
            refl
            (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))

    -- (XSL→Kelly) Kelly's symmetric-monoidal coherence theorem on the
    -- `permute` fragment, in its TRUE `≅↭`-CONDITIONED form (this is
    -- exactly `Categories.PermuteCoherence.Faithfulness.FaithfulnessResidual`,
    -- since APROP's `permute` IS that module's `permute`): two `permute`
    -- derivations between the same boundary whose evaluated finite
    -- bijections coincide (`eval-↭ p ≈-fb eval-↭ q`) are `≈Term`-equal.
    --
    -- This REPLACES the OLD `X-permute-self-loop-id : ∀ {xs} (r : xs ↭
    -- xs) → permute r ≈Term id`, which was FALSE in general (duplicate
    -- X-level lists give `permute σ ≢ id`).  The new field is TRUE
    -- (Kelly 1964); its `eval-↭`-hypothesis is discharged constructively
    -- at the (d) use site from the `Unique`-ness of the decoder stacks
    -- (see `stack-eval-coherence` + `Rigid.eval-rigid`).
    permute-≅↭-faithful
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → eval-↭ p ≈-fb eval-↭ q
      → permute p ≈Term permute q

    -- (F) Structural ↔ algorithmic decoder agreement.
    decode-rel-≈-decode
      : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f

--------------------------------------------------------------------------------
-- ## Section 3a: `buildFromResiduals` — construct `Build` from a
-- finer-grained set of 7 APROP-specific residuals.
--
-- This factors the trust into narrower obligations.  See
-- `FromAssumptions/{DecodeRelDecode,ProcessTermPermute}.agda` for the
-- residual records.

buildFromResiduals
  : (decodeShapeResiduals : DecodeShapeResiduals)
    (rhoShapeResidual : RhoShapeResidual)
    (agenSigmaResiduals : Residuals)
    (decode-rel-≈-decode-α⇒-impl
       : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C})
                   ≈Term decode (α⇒ {A} {B} {C}))
    (decode-rel-≈-decode-α⇐-impl
       : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C})
                   ≈Term decode (α⇐ {A} {B} {C}))
    (permute-≅↭-faithful-impl
       : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
       → eval-↭ p ≈-fb eval-↭ q → permute p ≈Term permute q)
    (processTermResidual : ProcessTermAligned2Residual)
  → Build
buildFromResiduals
    decodeShapeResiduals
    rhoShapeResidual
    agenSigmaResiduals
    decode-rel-≈-decode-α⇒-impl
    decode-rel-≈-decode-α⇐-impl
    permute-≅↭-faithful-impl
    processTermResidual = record
  { process-term-permute-aligned =
      PTP-sig.process-term-permute-aligned-impl processTermResidual
  ; permute-≅↭-faithful = permute-≅↭-faithful-impl
  ; decode-rel-≈-decode =
      DRD-sig.decode-rel-≈-decode-impl
        decodeShapeResiduals
        rhoShapeResidual
        agenSigmaResiduals
        decode-rel-≈-decode-α⇒-impl
        decode-rel-≈-decode-α⇐-impl
  }

--------------------------------------------------------------------------------
-- ## Section 4: CONSTRUCTIVE COMPOSITION.
--
-- `WithAssumptions` derives `decode-attempt-resp-iso`,
-- `decode-resp-iso`, and `decode-rel-resp-iso` constructively from
-- the three `Build` fields.

module WithAssumptions (b : Build) where
  open Build b public

  ------------------------------------------------------------------------
  -- Step 0: Reconstruct the old (c)/(d) discharge BODIES from the
  -- factored fields.

  private
    -- The (d) discharge needs Kelly's `≅↭`-conditioned coherence on
    -- `permute`.  That IS the `permute-≅↭-faithful` field directly.
    finalp-coherence : FinalPermuteN.PermuteCoherence
    finalp-coherence =
      record { permute-≈Term-coherence = permute-≅↭-faithful }

    open FinalPermuteN.WithCoherence finalp-coherence
      using (final-permute-absorb-discharge)

  -- The OLD (c) body.  The `process-term-permute-aligned` field already
  -- takes `stack-↭` as an explicit parameter, so we apply it DIRECTLY to
  -- the discharged (b) value `process-edges-resp-iso-stack f g iso`.  No
  -- Kelly coherence is needed for the (c) path.
  process-edges-resp-iso-term
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → let process-F = process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)
          process-G = process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)
          stack-↭ = process-edges-resp-iso-stack f g iso
      in permute (Perm.↭-sym stack-↭)
         ∘ subst₂ HomTerm
             (cong unflatten (full-dom-eq f g))
             refl
             (proj₂ process-G)
         ≈Term
         proj₂ process-F
  process-edges-resp-iso-term f g iso =
    process-term-permute-aligned f g iso

  -- The OLD (d) body, derived from `final-permute-absorb-discharge`
  -- applied to the discharged (b) value.
  final-permute-absorb
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ f ⟫F)
        (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ g ⟫F)
    → let stack-↭ = process-edges-resp-iso-stack f g iso
          F-vlab = Hypergraph.vlab ⟪ f ⟫F
          G-vlab = Hypergraph.vlab ⟪ g ⟫F
      in subst₂ HomTerm
           refl
           (cong unflatten (full-cod-eq f g))
           (permute-via-vlab G-vlab perm-g)
         ∘ permute stack-↭
         ≈Term
         permute-via-vlab F-vlab perm-f
  final-permute-absorb f g iso perm-f perm-g =
    final-permute-absorb-discharge f g iso
      (process-edges-resp-iso-stack f g iso) perm-f perm-g
      (stack-eval-coherence f g iso perm-f perm-g)

  ------------------------------------------------------------------------
  -- Step 1: `decode-attempt-resp-iso`.
  --
  -- The algorithmic-decoder iso invariance, derived constructively
  -- from the discharged (b), the locally-reconstructed old (c)/(d)
  -- bodies above, and `decode-attempt-Linear-extracts` plus the
  -- subst₂ algebra.

  decode-attempt-resp-iso
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → proj₁ (decode-attempt-Linear f)
      ≈Term subst₂ HomTerm
              (cong unflatten (full-dom-eq f g))
              (cong unflatten (full-cod-eq f g))
              (proj₁ (decode-attempt-Linear g))
  decode-attempt-resp-iso {A} {B} f g iso = chain
    where
      f-extract-data = decode-attempt-Linear-extracts-discharge f
      g-extract-data = decode-attempt-Linear-extracts-discharge g

      perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
               Perm.↭ Hypergraph.cod ⟪ f ⟫F
      perm-f = proj₁ f-extract-data

      perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
               Perm.↭ Hypergraph.cod ⟪ g ⟫F
      perm-g = proj₁ g-extract-data

      F-vlab = Hypergraph.vlab ⟪ f ⟫F
      G-vlab = Hypergraph.vlab ⟪ g ⟫F

      process-F-term = proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
      process-G-term = proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))

      final-permute-F = permute-via-vlab F-vlab perm-f
      final-permute-G = permute-via-vlab G-vlab perm-g

      dom-iso = full-dom-eq f g
      cod-iso = full-cod-eq f g

      stack-↭ = process-edges-resp-iso-stack f g iso
      proc-eq = process-edges-resp-iso-term f g iso
      fperm-eq = final-permute-absorb f g iso perm-f perm-g

      f-extracts : proj₁ (decode-attempt-Linear f)
                 ≡ final-permute-F ∘ process-F-term
      f-extracts = proj₂ f-extract-data

      g-extracts : proj₁ (decode-attempt-Linear g)
                 ≡ final-permute-G ∘ process-G-term
      g-extracts = proj₂ g-extract-data

      -- The new composition shape uses `permute (Perm.↭-sym stack-↭)`
      -- and `permute stack-↭` as bridges; their round-trip cancels by
      -- `permute-inverse-right`.

      -- The G-side terms after subst₂.
      subst-G-final = subst₂ HomTerm refl (cong unflatten cod-iso)
                              final-permute-G
      subst-G-proc  = subst₂ HomTerm (cong unflatten dom-iso) refl
                              process-G-term

      -- (d): `subst-G-final ∘ permute stack-↭ ≈Term final-permute-F`.
      -- (c): `permute (sym stack-↭) ∘ subst-G-proc ≈Term process-F-term`.
      -- Compose: `final-permute-F ∘ process-F-term ≈Term
      --   (subst-G-final ∘ permute stack-↭) ∘ (permute (sym stack-↭) ∘ subst-G-proc)`.
      -- By assoc + `permute-inverse-right stack-↭`:
      --   ≈Term subst-G-final ∘ id ∘ subst-G-proc
      --   ≈Term subst-G-final ∘ subst-G-proc                    [idˡ]
      --   ≡ subst₂ dom-iso cod-iso (final-permute-G ∘ process-G-term)  [subst₂-∘-distrib]
      --   ≡ subst₂ dom-iso cod-iso (decode-attempt-Linear g)    [sym g-extracts]
      -- And `decode-attempt-Linear f ≡ final-permute-F ∘ process-F-term` [f-extracts].

      ∘-step : final-permute-F ∘ process-F-term
             ≈Term (subst-G-final ∘ permute stack-↭)
                   ∘ (permute (Perm.↭-sym stack-↭) ∘ subst-G-proc)
      ∘-step = FM.∘-resp-≈ (≈-Term-sym fperm-eq) (≈-Term-sym proc-eq)

      cancellation-step
        : (subst-G-final ∘ permute stack-↭)
          ∘ (permute (Perm.↭-sym stack-↭) ∘ subst-G-proc)
          ≈Term subst-G-final ∘ subst-G-proc
      cancellation-step = begin
        (subst-G-final ∘ permute stack-↭)
          ∘ (permute (Perm.↭-sym stack-↭) ∘ subst-G-proc)
          ≈⟨ FM.assoc ⟩
        subst-G-final ∘ (permute stack-↭
          ∘ (permute (Perm.↭-sym stack-↭) ∘ subst-G-proc))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        subst-G-final ∘ ((permute stack-↭ ∘ permute (Perm.↭-sym stack-↭))
          ∘ subst-G-proc)
          ≈⟨ refl⟩∘⟨ (permute-inverse-right stack-↭ ⟩∘⟨refl) ⟩
        subst-G-final ∘ (id ∘ subst-G-proc)
          ≈⟨ refl⟩∘⟨ FM.identityˡ ⟩
        subst-G-final ∘ subst-G-proc
          ∎

      subst-fold : subst-G-final ∘ subst-G-proc
                 ≡ subst₂ HomTerm
                     (cong unflatten dom-iso)
                     (cong unflatten cod-iso)
                     (final-permute-G ∘ process-G-term)
      subst-fold = sym (subst₂-∘-distrib dom-iso refl cod-iso
                                          final-permute-G process-G-term)

      chain
        : proj₁ (decode-attempt-Linear f)
          ≈Term subst₂ HomTerm
                  (cong unflatten dom-iso)
                  (cong unflatten cod-iso)
                  (proj₁ (decode-attempt-Linear g))
      chain = begin
        proj₁ (decode-attempt-Linear f)
          ≈⟨ ≡⇒≈Term f-extracts ⟩
        final-permute-F ∘ process-F-term
          ≈⟨ ∘-step ⟩
        (subst-G-final ∘ permute stack-↭)
          ∘ (permute (Perm.↭-sym stack-↭) ∘ subst-G-proc)
          ≈⟨ cancellation-step ⟩
        subst-G-final ∘ subst-G-proc
          ≈⟨ ≡⇒≈Term subst-fold ⟩
        subst₂ HomTerm (cong unflatten dom-iso) (cong unflatten cod-iso)
          (final-permute-G ∘ process-G-term)
          ≈⟨ ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten dom-iso)
                                            (cong unflatten cod-iso))
                            (sym g-extracts)) ⟩
        subst₂ HomTerm (cong unflatten dom-iso) (cong unflatten cod-iso)
          (proj₁ (decode-attempt-Linear g))
          ∎

  ------------------------------------------------------------------------
  -- Step 2: `decode-resp-iso` (algorithmic level, with `decode`).
  --
  -- Lifts `decode-attempt-resp-iso` through the boundary subst₂ in
  -- `decode`'s definition.

  decode-resp-iso
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode f ≈Term decode g
  decode-resp-iso {A} {B} f g iso-T = chain
    where
      t-f = proj₁ (decode-attempt-Linear f)
      t-g = proj₁ (decode-attempt-Linear g)

      dom-bridge = full-dom-eq f g
      cod-bridge = full-cod-eq f g

      body-eq : t-f ≈Term subst₂ HomTerm (cong unflatten dom-bridge)
                                          (cong unflatten cod-bridge) t-g
      body-eq = decode-attempt-resp-iso f g iso-T

      lifted-eq
        : decode f
          ≈Term subst₂ HomTerm
                  (cong unflatten (⟪⟫F-domL f))
                  (cong unflatten (⟪⟫F-codL f))
                  (subst₂ HomTerm
                    (cong unflatten dom-bridge)
                    (cong unflatten cod-bridge)
                    t-g)
      lifted-eq = subst₂-resp-≈Term (⟪⟫F-domL f) (⟪⟫F-codL f) body-eq

      collapsed
        : subst₂ HomTerm
            (cong unflatten (⟪⟫F-domL f))
            (cong unflatten (⟪⟫F-codL f))
            (subst₂ HomTerm
              (cong unflatten dom-bridge)
              (cong unflatten cod-bridge)
              t-g)
          ≡ subst₂ HomTerm
              (cong unflatten (trans dom-bridge (⟪⟫F-domL f)))
              (cong unflatten (trans cod-bridge (⟪⟫F-codL f)))
              t-g
      collapsed = subst₂-HomTerm-trans dom-bridge (⟪⟫F-domL f)
                                        cod-bridge (⟪⟫F-codL f) t-g

      dom-collapse : trans dom-bridge (⟪⟫F-domL f) ≡ ⟪⟫F-domL g
      dom-collapse = trans-paths-collapse (⟪⟫F-domL f) (⟪⟫F-domL g)
        where
          trans-paths-collapse
            : ∀ {A : Set} {a b c : A} (p : a ≡ c) (q : b ≡ c)
            → trans (trans q (sym p)) p ≡ q
          trans-paths-collapse refl refl = refl

      cod-collapse : trans cod-bridge (⟪⟫F-codL f) ≡ ⟪⟫F-codL g
      cod-collapse = trans-paths-collapse (⟪⟫F-codL f) (⟪⟫F-codL g)
        where
          trans-paths-collapse
            : ∀ {A : Set} {a b c : A} (p : a ≡ c) (q : b ≡ c)
            → trans (trans q (sym p)) p ≡ q
          trans-paths-collapse refl refl = refl

      rewritten
        : subst₂ HomTerm
            (cong unflatten (trans dom-bridge (⟪⟫F-domL f)))
            (cong unflatten (trans cod-bridge (⟪⟫F-codL f)))
            t-g
          ≡ subst₂ HomTerm
              (cong unflatten (⟪⟫F-domL g))
              (cong unflatten (⟪⟫F-codL g))
              t-g
      rewritten = subst₂-cong-proofs (trans dom-bridge (⟪⟫F-domL f))
                                      (⟪⟫F-domL g)
                                      (trans cod-bridge (⟪⟫F-codL f))
                                      (⟪⟫F-codL g)
                                      t-g
                                      dom-collapse cod-collapse

      chain : decode f ≈Term decode g
      chain = ≈-Term-trans lifted-eq
                (≈-Term-trans (≡⇒≈Term collapsed)
                              (≡⇒≈Term rewritten))

  ------------------------------------------------------------------------
  -- Step 3: `decode-rel-resp-iso` (term level, with `decode-rel`).
  --
  -- Composes `decode-resp-iso` with the (F) decoder-agreement field.

  decode-rel-resp-iso
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode-rel f ≈Term decode-rel g
  decode-rel-resp-iso f g iso =
    ≈-Term-trans (decode-rel-≈-decode f)
      (≈-Term-trans (decode-resp-iso f g iso)
                    (≈-Term-sym (decode-rel-≈-decode g)))
