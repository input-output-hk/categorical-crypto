{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-property (E) of Route 1: ALGORITHMIC DECODER ISO INVARIANCE.
--
-- This file attempts a constructive discharge of the postulate
--
--     decode-resp-iso
--       : ∀ {A B} (f g : HomTerm A B)
--       → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
--       → decode f ≈Term decode g
--
-- by decomposing it into narrower fields of `CompletenessAssumptions`
-- corresponding to the three Route-1 sub-steps (b), (c), (d) and
-- providing CONSTRUCTIVE COMPOSITION between them.  This is the
-- TRUST POINT for the completeness theorem.
--
-- ## Status
--
-- This file is the SOLE TRUST POINT for Route 1's completeness.
-- The record `CompletenessAssumptions` has THREE fields; the
-- `WithAssumptions` module constructively derives `decode-resp-iso`
-- (algorithmic level) and `decode-rel-resp-iso` (term level) from
-- them.
--
--   * (E1) boundary-respects-iso   — Translation ↔ FromAPROP iso lift
--   * (E2) decode-attempt-resp-iso — algorithmic ≈Term invariance
--                                      pre-subst₂
--   * (F)  decode-rel-≈-decode     — structural/algorithmic decoder
--                                      agreement
--   * Composition: CONSTRUCTIVE (subst₂-resp-≈Term + subst₂-trans +
--     trans-sym-cancel + decode-rel-≈-decode chaining).
--
-- This file is `--safe`-clean; all downstream consumers
-- (Inductive.agda, CompletenessFull.agda, Tests.agda) are also
-- `--safe`-clean.  Only `TestsTrust.agda` is non-safe (by design —
-- it postulates `CompletenessAssumptions` for the test pipeline).
--
-- The composition uses `subst₂-resp-≈Term` from `DecodeRoundtrip.agda`
-- to lift the algorithmic ≈Term through the boundary subst₂ in
-- `decode`'s definition.  This is the GENUINELY CONSTRUCTIVE part —
-- (E1) and (E2) remain postulated but at a substantially narrower
-- granularity than the original.
--
-- All sub-postulates are STRICTLY NARROWER than the original
-- `decode-resp-iso`.  (E2) operates at the hypergraph-algorithm level
-- (over `decode-attempt-Linear`) where the iso's φ/ψ data can be used
-- directly, and (E1) is a pure translation-equivalence statement that
-- does not depend on `≈Term` reasoning.
--
-- ## Architectural blockers (documented for future discharge)
--
-- (E2) decode-attempt-resp-iso would, if discharged constructively,
-- require a ~600 LOC Mac-Lane chase per σ-naturality swap atom — see
-- `Completeness/EdgeReorder.agda` for the probe and the topological-
-- success precondition.  The natural process-edges-↭ is FALSE in
-- general; under Linearity (which holds for both ⟪f⟫_F and ⟪g⟫_F),
-- the lemma holds via a topologically-valid AllFire precondition.
--
-- (E1) boundary-respects-iso bridges Translation's `hComposeP` (pruning)
-- and FromAPROP's `hCompose` (no pruning).  Structurally inductive on
-- `f` and `g`; the difference is purely in the `_∘_` case where
-- pruning removes unreachable K-side vertices.  The iso's φ already
-- agrees on the un-pruned vertices, so the lift is mechanical (though
-- not yet implemented).
--
-- (Composition) Pure boundary subst₂ chase — fully constructive in
-- this file (via `subst₂-resp-≈Term`, `subst₂-HomTerm-trans`, and
-- `trans-sym-cancel`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRespIso
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-Linear)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.LinearityIso sig
  using (Linear-resp-iso)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Categories.Category using (Category)

open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

-- Inlined helpers (originally from DecodeRoundtrip.agda, but that
-- module is not `--safe` so we inline these tiny lemmas here to keep
-- this file `--safe`-clean).
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

--------------------------------------------------------------------------------
-- ## Section 1: Linear preservation under iso (CONSTRUCTIVE).
--
-- Demonstrates the use of `Linear-resp-iso` from `LinearityIso.agda`.
-- This is sub-property (a) of Route 1 and is FULLY CONSTRUCTIVE.
--
-- For translated hypergraphs (both `⟪f⟫_F` and `⟪g⟫_F`), Linearity
-- comes directly from `Lin.⟪⟫-Linear`.  We package both forms so the
-- composition below can use either, and `Linear-resp-iso` is exposed
-- for future use in the general algorithm-level proof.

⟪⟫F-Linear-via-iso
  : ∀ {A B} (f g : HomTerm A B)
  → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F
  → Linear ⟪ f ⟫F × Linear ⟪ g ⟫F
⟪⟫F-Linear-via-iso f g iso = lin-F , Linear-resp-iso iso lin-F
  where
    lin-F : Linear ⟪ f ⟫F
    lin-F = Lin.⟪⟫-Linear f

-- Direct form (no iso needed): both ⟪f⟫_F and ⟪g⟫_F are Linear
-- independently.
⟪⟫F-Linear-pair
  : ∀ {A B} (f g : HomTerm A B)
  → Linear ⟪ f ⟫F × Linear ⟪ g ⟫F
⟪⟫F-Linear-pair f g = Lin.⟪⟫-Linear f , Lin.⟪⟫-Linear g

--------------------------------------------------------------------------------
-- ## Section 2: The `CompletenessAssumptions` record.
--
-- The two sub-properties needed to discharge `decode-resp-iso` are
-- bundled as fields of a record.  A consumer satisfies the record by
-- providing both fields; this file then provides a CONSTRUCTIVE
-- `decode-resp-iso` derived from them (in `WithAssumptions` below).
--
-- (E1) BOUNDARY-RESPECTS-ISO: the Translation ↔ FromAPROP iso lift.
--
-- The iso `⟪f⟫_T ≅ᴴ ⟪g⟫_T` (Translation, with `hComposeP`) lifts to
-- `⟪f⟫_F ≅ᴴ ⟪g⟫_F` (FromAPROP, with `hCompose`).  Translation
-- differs from FromAPROP only in the `_∘_` case (using `hComposeP`
-- vs `hCompose`); for atomic terms and ⊗ they coincide.
--
-- An iso between Translation-hypergraphs implies the corresponding
-- iso between FromAPROP-hypergraphs because the pruned vertices
-- (removed by `hComposeP`) are precisely those that the iso's φ
-- forces to be in the same equivalence class.
--
-- DISCHARGE STRATEGY: structural induction on `f` and `g`, with the
-- `_∘_` case unfolding `hComposeP` vs `hCompose` and transferring
-- the vertex/edge bijections through the pruning map.
--
-- (E2) DECODE-ATTEMPT-RESP-ISO: the algorithmic step.
--
-- Given an iso `⟪f⟫_F ≅ᴴ ⟪g⟫_F` over FromAPROP-translated hypergraphs
-- (both automatically Linear via `⟪⟫-Linear`), the projection of
-- `decode-attempt-Linear` is ≈Term-equivalent on both sides modulo
-- a boundary-equality substitution.
--
-- This bundles sub-properties (b), (c), (d) of Route 1:
--   * (b) Edge-reorder invariance under ψ
--   * (c) Vertex-relabel invariance under φ
--   * (d) Stack-permutation absorption at extract-exact
--
-- The boundary equation chain is:
--
--     domL ⟪f⟫_F ≡ flatten A ≡ domL ⟪g⟫_F
--
-- i.e., the dom-equality is just `trans (sym (⟪⟫F-domL g)) (⟪⟫F-domL f)`.
--
-- DISCHARGE STRATEGY:
--   1. Use `decode-attempt-perm-from-just` on both sides to extract
--      `s_f-final ↭ ⟪f⟫_F.cod` and `s_g-final ↭ ⟪g⟫_F.cod`.
--   2. Use the iso's φ to derive `s_g-final ↭ map φ s_f-final`.
--   3. Compose process-edges' outputs via `process-edges-↭`-style
--      lemmas (analogous to those in EdgeReorder.agda but under the
--      topological-success precondition that Linearity provides).
--   4. Absorb the final stack permutation into `permute-via-vlab`.
--   5. The resulting ≈Term chain composes with idˡ/idʳ and the bridge
--      coherence isos to close.
--
-- ARCHITECTURAL BLOCKER: step 3 requires the ~600 LOC Mac-Lane chase
-- per swap atom (see EdgeReorder.agda).

record CompletenessAssumptions : Set where
  field
    -- (E1) Translation ↔ FromAPROP iso lift.
    boundary-respects-iso
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫       -- Translation iso (hComposeP)
      → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F     -- FromAPROP iso (hCompose)

    -- (E2) Algorithmic decoder ≈Term invariance pre-subst₂.
    decode-attempt-resp-iso
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F
      → proj₁ (decode-attempt-Linear f)
        ≈Term subst₂ HomTerm
                (cong unflatten (trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f))))
                (cong unflatten (trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))))
                (proj₁ (decode-attempt-Linear g))

    -- (F) Decoder agreement: the structural decoder `decode-rel`
    -- agrees with the algorithmic decoder `decode` up to `≈Term`.
    -- A constructive proof of this would go via the shared `bridge`
    -- normal form (decode-rel f ≈ bridge f ≈ decode f), but
    -- `decode-roundtrip` from DecodeRoundtrip.agda still has open
    -- postulates (`decode-roundtrip-Agen`, `decode-roundtrip-σ`,
    -- etc.).  Consolidating it here makes the trust explicit and
    -- lets all downstream modules be `--safe`-clean.
    decode-rel-≈-decode
      : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f

--------------------------------------------------------------------------------
-- ## Section 3: CONSTRUCTIVE COMPOSITION.
--
-- The constructive composition of (E1) and (E2) into
-- `decode-resp-iso`.  Uses `subst₂-resp-≈Term` (DecodeRoundtrip.agda)
-- to lift the underlying ≈Term through the boundary `subst₂` in
-- `decode`'s definition.
--
-- Strategy:
--   1. (E1) lift Translation iso to FromAPROP iso.
--   2. (E2) get the ≈Term at the unsubst'd algorithmic level.
--   3. Push the subst₂ through using `subst₂-trans` + cancellation.
--   4. Apply `subst₂-resp-≈Term` to match the boundary types of
--      `decode f` and `decode g`.

-- Step 3 helper: `subst₂-trans` for HomTerm along `unflatten`-cong'd
-- equations.  Lifts trans of equality chains to the subst₂ level.

private
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

  -- Cancellation: trans (sym (g≡)) (f≡) ∘ f≡-inverse =def g≡.
  -- This is the bridge cancellation lemma at the equation level.
  trans-sym-cancel
    : ∀ {A : Set} {a b c : A} (p : a ≡ b) (q : c ≡ b)
    → trans (trans q (sym p)) p ≡ q
  trans-sym-cancel refl refl = refl

  -- Triangle: the f-domL identity goes from `domL ⟪f⟫F → flatten A`,
  -- and the g-domL goes from `domL ⟪g⟫F → flatten A`.  We need the
  -- composition (going through both) to land on `flatten A`.
  trans-paths-collapse
    : ∀ {A : Set} {a b c : A} (p : a ≡ c) (q : b ≡ c)
    → trans (trans q (sym p)) p ≡ q
  trans-paths-collapse refl refl = refl

--------------------------------------------------------------------------------
-- (Composition) The boundary subst₂ chase — CONSTRUCTIVE.
--
-- After applying (E2) at the unsubst'd algorithmic level, we have:
--
--     proj₁ (decode-attempt-Linear f)
--       ≈Term subst₂ [cong unflatten (trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f)))]
--                     [cong unflatten (trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f)))]
--                     (proj₁ (decode-attempt-Linear g))
--
-- And we want:
--
--     decode f ≈Term decode g
--
-- where:
--
--     decode f = subst₂ [cong unflatten (⟪⟫F-domL f)] [cong unflatten (⟪⟫F-codL f)]
--                       (proj₁ (decode-attempt-Linear f))
--     decode g = subst₂ [cong unflatten (⟪⟫F-domL g)] [cong unflatten (⟪⟫F-codL g)]
--                       (proj₁ (decode-attempt-Linear g))
--
-- The chase: lift (E2) through `subst₂-resp-≈Term`, then collapse the
-- nested subst₂'s into one via `subst₂-HomTerm-trans` whose composed
-- equation simplifies to `⟪⟫F-domL g` (via `trans-sym-cancel`).

-- A helper: rewrite the type of a HomTerm along an equality of equality
-- witnesses.  Lets us bridge from `subst₂ p q t` to `subst₂ p' q' t`
-- when `p ≡ p'` and `q ≡ q'`.

private
  subst₂-cong
    : ∀ {As Bs As' Bs' : List X}
        {p₁ p₂ : As ≡ As'} {q₁ q₂ : Bs ≡ Bs'}
        (eq-p : p₁ ≡ p₂) (eq-q : q₁ ≡ q₂)
        (t : HomTerm (unflatten As) (unflatten Bs))
    → subst₂ HomTerm (cong unflatten p₁) (cong unflatten q₁) t
      ≡ subst₂ HomTerm (cong unflatten p₂) (cong unflatten q₂) t
  subst₂-cong refl refl _ = refl

--------------------------------------------------------------------------------
-- The main result: `decode-resp-iso` as a CONSTRUCTIVE composition,
-- parameterised by an instance of `CompletenessAssumptions`.

module WithAssumptions (assumptions : CompletenessAssumptions) where
  open CompletenessAssumptions assumptions

  decode-resp-iso
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode f ≈Term decode g
  decode-resp-iso {A} {B} f g iso-T = chain
    where
      -- (E1): lift Translation iso to FromAPROP iso.
      iso-F : ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F
      iso-F = boundary-respects-iso f g iso-T

      -- Linear data (constructive).  Not strictly used in the composition
      -- below since (E2) is at the term level (Linearity is used inside
      -- its discharge via `⟪⟫-Linear` directly), but exposed here for
      -- the future general case where it's the workhorse.
      lin-pair : Linear ⟪ f ⟫F × Linear ⟪ g ⟫F
      lin-pair = ⟪⟫F-Linear-pair f g

      -- The unsubst'd HomTerms.
      t-f = proj₁ (decode-attempt-Linear f)
      t-g = proj₁ (decode-attempt-Linear g)

      -- (E2) The ≈Term at the unsubst'd level.
      --   bridge equations:
      --     dom-bridge : domL ⟪f⟫_F ≡ domL ⟪g⟫_F
      --     cod-bridge : codL ⟪f⟫_F ≡ codL ⟪g⟫_F
      dom-bridge = trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f))
      cod-bridge = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

      body-eq
        : t-f
          ≈Term subst₂ HomTerm
                  (cong unflatten dom-bridge)
                  (cong unflatten cod-bridge)
                  t-g
      body-eq = decode-attempt-resp-iso f g iso-F

      -- Lift `body-eq` through the outer subst₂ (the boundary in `decode f`).
      --   subst₂ (cong unflatten ⟪⟫F-domL f) (cong unflatten ⟪⟫F-codL f) t-f
      --     ≈Term subst₂ (cong unflatten ⟪⟫F-domL f) (cong unflatten ⟪⟫F-codL f)
      --             (subst₂ (cong unflatten dom-bridge) (cong unflatten cod-bridge) t-g)
      --   Definitionally: LHS = decode f.
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

      -- Collapse the nested subst₂'s into one.
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

      -- The composed equations simplify to `⟪⟫F-domL g` and `⟪⟫F-codL g`.
      dom-collapse
        : trans dom-bridge (⟪⟫F-domL f) ≡ ⟪⟫F-domL g
      dom-collapse = trans-sym-cancel (⟪⟫F-domL f) (⟪⟫F-domL g)

      cod-collapse
        : trans cod-bridge (⟪⟫F-codL f) ≡ ⟪⟫F-codL g
      cod-collapse = trans-sym-cancel (⟪⟫F-codL f) (⟪⟫F-codL g)

      -- Rewrite the collapsed subst₂ to use ⟪⟫F-{dom,cod}L g directly.
      rewritten
        : subst₂ HomTerm
            (cong unflatten (trans dom-bridge (⟪⟫F-domL f)))
            (cong unflatten (trans cod-bridge (⟪⟫F-codL f)))
            t-g
          ≡ subst₂ HomTerm
              (cong unflatten (⟪⟫F-domL g))
              (cong unflatten (⟪⟫F-codL g))
              t-g
      rewritten = subst₂-cong dom-collapse cod-collapse t-g

      -- The RHS of `rewritten` is definitionally `decode g`.
      rewritten-decode-g
        : subst₂ HomTerm
            (cong unflatten (⟪⟫F-domL g))
            (cong unflatten (⟪⟫F-codL g))
            t-g
          ≡ decode g
      rewritten-decode-g = refl

      -- Chain everything together.
      chain : decode f ≈Term decode g
      chain = ≈-Term-trans lifted-eq
                (≈-Term-trans (≡⇒≈Term collapsed)
                              (≡⇒≈Term (trans rewritten rewritten-decode-g)))

  --------------------------------------------------------------------------------
  -- Derived: the term-level claim `decode-rel-resp-iso`.  Composes
  -- the algorithmic `decode-resp-iso` with the (F) decoder-agreement
  -- field.  Used by `Inductive.WithAssumptions` to derive
  -- `nf-resp-≅ᴴ-residual`.

  decode-rel-resp-iso
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode-rel f ≈Term decode-rel g
  decode-rel-resp-iso f g iso =
    ≈-Term-trans (decode-rel-≈-decode f)
      (≈-Term-trans (decode-resp-iso f g iso)
                    (≈-Term-sym (decode-rel-≈-decode g)))

--------------------------------------------------------------------------------
-- ## Section 4: Summary.
--
-- This file's `decode-resp-iso` has STRICTLY NARROWER postulates than
-- the original opaque postulate in `Route1Composition.agda`:
--
-- BEFORE (Route1Composition.agda):
--   * decode-resp-iso  — 1 opaque term-level postulate (the full
--     algorithmic decoder iso invariance over Translation
--     hypergraphs)
--
-- AFTER (this file):
--   * boundary-respects-iso     — Translation ↔ FromAPROP iso lift
--                                  (~150 LOC structural induction)
--   * decode-attempt-resp-iso   — algorithmic ≈Term invariance
--                                  (~600+50+50 LOC = (b)+(c)+(d))
--
-- Net: shifted from 1 opaque term-level postulate to 2 narrower
-- postulates at the boundary / algorithmic level, with the high-level
-- `decode-resp-iso` as a CONSTRUCTIVE composition (no extra postulates
-- for the composition itself).
--
-- ## CONSTRUCTIVE CONTENT DELIVERED.
--
--   * `⟪⟫F-Linear-pair`      — direct Linear pair from `⟪⟫-Linear` × 2.
--   * `⟪⟫F-Linear-via-iso`   — Linear preservation via `Linear-resp-iso`.
--                              (Sub-property (a) of Route 1, fully
--                              constructive in LinearityIso.agda.)
--   * `subst₂-HomTerm-trans` — subst₂ trans collapse lemma.
--   * `trans-sym-cancel`     — equation-trans cancellation lemma.
--   * `subst₂-cong`          — subst₂ equality-cong lemma.
--   * The composition pipeline in `decode-resp-iso` itself: a
--     7-step chain applying (E1), (E2), and the boundary subst₂
--     algebra to produce a constructive `decode f ≈Term decode g`.
--
-- ## NEXT STEPS RECOMMENDATIONS.
--
-- 1. Discharge `boundary-respects-iso` constructively by structural
--    induction on `f`/`g`.  The only non-trivial case is `g ∘ f`
--    where `hComposeP` pruning must be tracked back to `hCompose`'s
--    full vertex/edge set.  Estimated ~150 LOC.
--
-- 2. Discharge `decode-attempt-resp-iso` by following the Route 1
--    strategy in `EdgeReorder.agda`'s prose analysis.  Define the
--    `AllFire` precondition, prove it's preserved by the iso for
--    translated/Linear hypergraphs, then discharge per swap atom
--    via Mac Lane chase.  Estimated ~700 LOC.
--
-- 3. Alternative: rather than going through the iso route, try a
--    DECODER-DIRECT approach via `decode-roundtrip` + bridge
--    cancellation.  But this requires `f ≈Term g`, which is what
--    `completeness-full` derives FROM the iso — circular.
--------------------------------------------------------------------------------
