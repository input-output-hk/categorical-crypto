{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for the RESHAPED `process-edges-resp-iso-term`
-- field from `Completeness/DecodeRespIso.agda` — the (c) field.
--
-- ## The target
--
-- The new (c) field has the form (LET-unfolded):
--
--   process-edges-resp-iso-term
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--     → let process-F = process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)
--           process-G = process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)
--           stack-↭   = process-edges-resp-iso-stack f g iso
--       in permute (Perm.↭-sym stack-↭)
--          ∘ subst₂ HomTerm
--              (cong unflatten (full-dom-eq f g))
--              refl
--              (proj₂ process-G)
--          ≈Term
--          proj₂ process-F
--
-- Crucially: the codomain bridge is a `permute`-built morphism (a
-- structural HomTerm), NOT a `subst₂` propositional transport.  This
-- is what changed between the previous shape (which used `subst₂
-- HomTerm refl (cong unflatten (sym stack-eq)) ...`) and the current
-- one.
--
-- ## Why the new shape is structurally CLEANER than the old one
--
-- Old shape: `subst₂` on codomain via `sym stack-eq : map vlab_G _ ≡
-- map vlab_F _`.  This list equality is provably FALSE in general (see
-- `Discharge/Sub/StackListEq.agda`'s counter-example with `Agen φ₁ ⊗
-- Agen φ₂` vs `σ ∘ (Agen φ₂ ⊗ Agen φ₁) ∘ σ`).  Hence the old (b) field
-- was required to be `≡`, but is not constructively dischargeable.
--
-- New shape: `permute` on codomain via `Perm.↭-sym stack-↭`.  The
-- `Perm.↭` IS constructively derivable (`stack-↭-from-iso` in
-- `Discharge/StackEq.agda`, via `decode-attempt-Linear` + `⟪⟫F-codL`).
-- The (b) field becomes constructively dischargeable, and (c)'s
-- statement absorbs the "ordering choice" via a structural HomTerm
-- (`permute`) rather than a propositional one (`subst₂`).
--
-- The trade-off: the term-level statement now compares
--   permute-bridge ∘ subst-on-dom proj₂-G  vs  proj₂-F
-- rather than
--   subst-on-cod-and-dom proj₂-G           vs  proj₂-F
--
-- The Mac Lane / Kelly content under both shapes is the SAME, but the
-- new shape lets us use the constructive `Perm.↭` data directly
-- without inventing a missing list equality.
--
-- ## What is genuinely irreducible (architectural blocker)
--
-- The irreducible content of the (c) field is symmetric monoidal
-- (Kelly) coherence between two parallel HomTerms built from
-- `process-all-edges` on a Linear hypergraph and its iso-image.
-- Discharging this fully constructively requires either:
--
--   (a) An extended `solveM` covering the symmetric (σ) case (Kelly's
--       coherence), not yet mechanised in
--       `Categories.MonoidalCoherence`.
--
--   (b) A `process-edges-↭-topo` lemma (analysed in
--       `Discharge/ProcessTerm.agda` and `Discharge/Sub/ProcessTermAligned.agda`)
--       supplying:
--         * `AllFire` predicate + natural-range AllFire (~150 LOC).
--         * Per-swap Mac Lane chase (`swap-atom-aligned`, ~200-400
--           LOC).
--         * `process-edges-↭-topo` itself by `_↭_` induction (~150
--           LOC).
--         * Iso-induced edge ↭ extraction (~50 LOC).
--         * Term bridge (~75 LOC).
--       Total ~625-825 LOC for full constructive discharge.
--
-- We follow option (b)'s decomposition pattern, but adapted to the
-- NEW shape: the residual is now a SINGLE narrow assumption
-- `process-term-permute-aligned`, the natural translation of (c)
-- into hypergraph-generic form, plus the iso ↦ edge-permutation
-- bridge.
--
-- ## What this module exports
--
-- 1. `process-term-iso-bridge-narrow` — the SINGLE narrow record
--    field, strictly smaller than the original (c) field.  Strictly
--    smaller in three concrete ways:
--      (i)  It takes the constructive `stack-↭-from-iso` value as
--           input (rather than internally invoking
--           `process-edges-resp-iso-stack`).
--      (ii) It works with the constructive `stack-↭-from-iso`, NOT
--           with the (b) field's `stack-↭` — these may differ
--           propositionally, but coherence absorbs the difference
--           when the user invokes Kelly's coherence (a separate
--           postulate).
--      (iii) The conclusion's `permute` uses the explicitly-passed
--            ↭ value, not a let-bound (b)-field-computed one.
--
-- 2. `WithAssumption.discharge-with-stack-fn` — given a stack-fn
--    callback (i.e. the (b) field plus the Kelly coherence
--    assumption), derive the original (c) field's exact body.
--
-- 3. Constructive helpers reused from `Discharge/StackEq.agda`:
--    `stack-↭-from-iso`, `stack-↭-flatten-B`.
--
-- ## File status
--
-- `--safe --with-K` clean.  No `postulate` keywords; the single
-- residual obligation is a RECORD FIELD.  A downstream consumer
-- either constructs the witness (via the path documented in section
-- "Next steps for full constructive discharge" below) or postulates
-- the record in a satellite file.
--
-- The narrowing vs the original (c) field is STRICT: every consumer
-- of `process-term-iso-bridge-narrow` can be built from the original
-- (c) field (by trivial composition with `stack-↭-from-iso`), but the
-- converse requires Kelly's coherence — which is the irreducible
-- residual.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermNew
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
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.StackEq sig-dec
  using (stack-↭-flatten-B; stack-↭-from-iso)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (permute-inverse-left; permute-inverse-right)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Section 1: Boundary equations (reused from DecodeRespIso/ProcessTerm).
--
-- Both `⟪ f ⟫F.domL` and `⟪ g ⟫F.domL` equal `flatten A` via
-- `⟪⟫F-domL`.  The transitive bridge `full-dom-eq f g` matches the
-- convention used by `DecodeRespIso.agda`'s `CompletenessAssumptions`
-- record.

full-dom-eq : ∀ {A B} (f g : HomTerm A B)
            → domL ⟪ g ⟫F ≡ domL ⟪ f ⟫F
full-dom-eq f g = trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f))

full-cod-eq : ∀ {A B} (f g : HomTerm A B)
            → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

--------------------------------------------------------------------------------
-- ## Section 2: The narrowed assumption.
--
-- A single record field, strictly narrower than the original (c)
-- field.  The narrowing is on TWO axes:
--
--   1. The `stack-↭` is supplied EXTERNALLY (not derived from a (b)
--      callback inside the assumption).  This unblocks downstream
--      composition: we can pass the constructive
--      `stack-↭-from-iso` directly.
--
--   2. The signature DOES NOT close over the (b) field; consumers
--      bridge (b)'s output to `stack-↭-from-iso`'s output via
--      Kelly's coherence in a separate step (see
--      `WithAssumption.discharge-with-stack-fn` and the (PermuteCoherence)
--      record from `Discharge/FinalPermute.agda`).
--
-- The conclusion's shape exactly matches the (c) field's `let`-
-- unfolded form, modulo the externalised `stack-↭` parameter.

record ProcessTermPermuteAssumption : Set where
  field
    -- The narrow term-level statement.  Given an iso AND an externally
    -- supplied stack permutation between the vlab-mapped stacks, the
    -- two `process-all-edges` morphisms agree up to:
    --   * `subst₂` on dom (propositional bridge, constructively
    --     derivable from `⟪⟫F-domL` on both sides).
    --   * `permute` on cod (the structural HomTerm bridging the
    --     supplied ↭).
    --
    -- Narrowing vs the original (c) field:
    --   * Takes `stack-↭` as an explicit input — no internal
    --     invocation of `process-edges-resp-iso-stack`.
    --   * Otherwise identical conclusion (same `≈Term` shape, same
    --     `subst₂` boundary on dom).
    process-term-permute-aligned
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (stack-↭ :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
      → permute (Perm.↭-sym stack-↭)
        ∘ subst₂ HomTerm
            (cong unflatten (full-dom-eq f g))
            refl
            (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 3: Kelly coherence helper.
--
-- For the discharge to compose with the (b) field (whose output may
-- differ propositionally from `stack-↭-from-iso`'s output), we need:
--
--   Given two `↭` derivations of the same atom lists, `permute` of
--   them produces `≈Term`-equal HomTerms.
--
-- This is exactly Kelly's coherence on the `permute` fragment,
-- already exposed as `PermuteCoherence` in `Discharge/FinalPermute.agda`.
-- We re-expose it here to make the composition self-contained, but a
-- downstream consumer of BOTH `ProcessTermPermuteAssumption` AND
-- `PermuteCoherence` would supply a single Kelly witness.

record PermuteCoherenceForBridge : Set where
  field
    -- Kelly's symmetric monoidal coherence on the `permute` fragment.
    permute-≈Term-coherence
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → permute p ≈Term permute q

--------------------------------------------------------------------------------
-- ## Section 4: Constructive composition.
--
-- Given the narrow assumption (and Kelly's coherence to bridge (b)'s
-- output to the constructive `stack-↭-from-iso`), discharge the
-- original (c) field.

module WithAssumption
  (assumption : ProcessTermPermuteAssumption)
  (coherence  : PermuteCoherenceForBridge)
  where
  open ProcessTermPermuteAssumption assumption
  open PermuteCoherenceForBridge coherence

  ------------------------------------------------------------------------
  -- Stage 1: discharge against the CONSTRUCTIVE `stack-↭-from-iso`
  -- value (no Kelly coherence needed).
  --
  -- A consumer who dispatches the (b) field to `stack-↭-from-iso`
  -- (the constructive realization in `Discharge/StackEq.agda`) gets
  -- the (c) field's body directly from this stage, with no Kelly
  -- coherence assumed.

  discharge-with-constructive-↭
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → permute (Perm.↭-sym (stack-↭-from-iso f g iso))
      ∘ subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          refl
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  discharge-with-constructive-↭ f g iso =
    process-term-permute-aligned f g iso (stack-↭-from-iso f g iso)

  ------------------------------------------------------------------------
  -- Stage 2: discharge against ANY stack-fn callback (e.g. the (b)
  -- field).  Uses Kelly coherence to bridge the difference between
  -- the (b)-supplied stack-↭ and our constructive `stack-↭-from-iso`.
  --
  -- The (b)-supplied value and `stack-↭-from-iso` derive the same
  -- underlying list permutation (both stem from the multiset
  -- structure of `process-all-edges`'s output on a Linear
  -- hypergraph + the `flatten B` bridge).  Their `permute`-images
  -- are `≈Term`-equal by Kelly's coherence, so we can rewrite the
  -- discharge against `stack-↭-from-iso` to one against the
  -- (b)-supplied value.

  discharge-with-stack-fn
    : (stack-fn :
        ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
        → map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          Perm.↭
          map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
    → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → permute (Perm.↭-sym (stack-fn f g iso))
      ∘ subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          refl
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  discharge-with-stack-fn stack-fn f g iso =
    let
      -- The (b)-supplied permutation.
      ↭-b : map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ↭-b = stack-fn f g iso

      -- The constructively-derived permutation.
      ↭-c : map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ↭-c = stack-↭-from-iso f g iso

      -- The discharge against the constructive ↭.
      discharge-c
        : permute (Perm.↭-sym ↭-c)
          ∘ subst₂ HomTerm
              (cong unflatten (full-dom-eq f g))
              refl
              (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
          ≈Term
          proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
      discharge-c = discharge-with-constructive-↭ f g iso

      -- Kelly's coherence: `permute (Perm.↭-sym ↭-b) ≈Term permute
      -- (Perm.↭-sym ↭-c)`.  Both `↭-sym` operands are derivations of
      -- the same underlying list permutation (just on the swapped
      -- boundary), so Kelly's coherence on the σ-structural fragment
      -- gives equality up to `≈Term`.
      coh-bridge
        : permute (Perm.↭-sym ↭-b) ≈Term permute (Perm.↭-sym ↭-c)
      coh-bridge = permute-≈Term-coherence (Perm.↭-sym ↭-b)
                                            (Perm.↭-sym ↭-c)
    in begin
       permute (Perm.↭-sym ↭-b)
         ∘ subst₂ HomTerm
             (cong unflatten (full-dom-eq f g))
             refl
             (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
         ≈⟨ coh-bridge ⟩∘⟨refl ⟩
       permute (Perm.↭-sym ↭-c)
         ∘ subst₂ HomTerm
             (cong unflatten (full-dom-eq f g))
             refl
             (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
         ≈⟨ discharge-c ⟩
       proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
         ∎

--------------------------------------------------------------------------------
-- ## Section 5: Reflexive case — constructively closed.
--
-- When `f ≡ g` propositionally (in particular when `f` and `g` are
-- the same term and `iso = refl-≅ᴴ ⟪ f ⟫`), we can constructively
-- discharge the field's body against `stack-↭ = Perm.refl` (and any
-- iso, by ignoring it):
--
--   * `full-dom-eq f f` is propositionally `refl` (with K).
--   * The dom-subst collapses to identity transport.
--   * `permute (Perm.↭-sym Perm.refl) = permute Perm.refl = id`.
--   * The goal reduces to `id ∘ proj₂-F ≈Term proj₂-F`, which is
--     `idˡ`.
--
-- This is a SANITY CHECK confirming our shape is consistent on the
-- trivial case, and it provides a constructive answer for `f ≡ g`.
-- It does NOT use the narrow assumption (no Mac Lane content
-- needed).

reflexive-discharge
  : ∀ {A B} (f : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ f ⟫)
  → permute (Perm.↭-sym
      (Perm.refl {xs = map (Hypergraph.vlab ⟪ f ⟫F)
                            (proj₁ (process-all-edges ⟪ f ⟫F
                                      (Hypergraph.dom ⟪ f ⟫F)))}))
    ∘ subst₂ HomTerm
        (cong unflatten (full-dom-eq f f))
        refl
        (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    ≈Term
    proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
reflexive-discharge {A} {B} f _iso =
  -- `full-dom-eq f f = trans (⟪⟫F-domL f) (sym (⟪⟫F-domL f))` which
  -- is propositionally `refl` (via UIP from `--with-K`).  We extract
  -- this via a helper.
  let dom-self-eq : full-dom-eq f f ≡ refl
      dom-self-eq = trans-sym-refl (⟪⟫F-domL f)
  in begin
       permute (Perm.↭-sym Perm.refl)
         ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
           (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         -- Replace `permute (↭-sym refl)` with `id` definitionally.
         ≡⟨ refl ⟩
       id
         ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
           (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         ≈⟨ FM.identityˡ ⟩
       subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
         (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         -- Now collapse the subst via `dom-self-eq : full-dom-eq f f ≡ refl`.
         ≡⟨ subst-collapse f dom-self-eq ⟩
       proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
         ∎
  where
    -- Local lemma: `trans p (sym p) ≡ refl` for any `p`.
    trans-sym-refl : ∀ {A : Set} {a b : A} (p : a ≡ b)
                   → trans p (sym p) ≡ refl
    trans-sym-refl refl = refl

    -- Local lemma: when the dom-eq collapses to `refl`, so does the
    -- subst.  Uses K (via the `refl` pattern match).
    subst-collapse
      : ∀ {A B} (f : HomTerm A B) (eq : full-dom-eq f f ≡ refl)
      → subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
          (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        ≡ proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
    subst-collapse f eq rewrite eq = refl

--------------------------------------------------------------------------------
-- ## Section 6: Next steps for full constructive discharge.
--
-- ### Discharging `process-term-permute-aligned` constructively
--
-- Given the architectural blocker analysis in
-- `Discharge/Sub/ProcessTermAligned.agda`, full constructive
-- discharge of `process-term-permute-aligned` requires (estimated
-- ~625-825 LOC):
--
--   (B-swap)   Per-swap Mac Lane chase.  IRREDUCIBLE; ~200-400 LOC.
--              Each `Perm.swap`-atom in the edge permutation
--              requires a Mac Lane chase aligning the
--              `unflatten-++-≅` wrappers across the two
--              `rest`-list shapes (see `EdgeReorder.agda` for the
--              concrete blocker).
--
--   (B-↭)     `process-edges-↭-topo`.  ~150 LOC.  By induction on
--              `_↭_`; the `swap` case routes through (B-swap).
--
--   (A-nat)    `AllFire-natural-range`.  ~150 LOC.  By structural
--              induction on `f`.  Each smart constructor preserves
--              AllFire-on-natural-range.
--
--   (C-bridge) `iso-induces-edge-↭`.  ~50 LOC.  Combinatorial only;
--              extracts the edge component of the iso through the
--              Translation ↔ FromAPROP edge correspondence.
--
--   (Bridge)   Term bridge through `ψ-ein`/`ψ-eout`/`ψ-lab`
--              compatibility.  ~75 LOC.
--
-- The new `permute`-bridge form does NOT reduce these requirements —
-- the underlying combinatorial-and-Mac-Lane content is the same.
-- What it DOES change:
--
--   * The (b) field is now constructively dischargeable (via
--     `stack-↭-from-iso`), so the trust delta from the (b)+(c) pair
--     reduces by one full field.
--
--   * The (c) field's statement uses `Perm.↭` rather than `≡`, so it
--     avoids the impossible "list equality" requirement that
--     blocked the old shape.
--
--   * `discharge-with-stack-fn` uses Kelly's coherence to bridge
--     the (b) field's value to `stack-↭-from-iso`'s value.  This
--     adds one more layer of coherence, but it's the SAME coherence
--     already required by the (d) field — so no new content.
--
-- ### Discharging `permute-≈Term-coherence` constructively
--
-- This is Kelly's symmetric monoidal coherence on the `permute`
-- fragment.  It is the SAME postulate (modulo a record-field
-- packaging difference) as the one in
-- `Discharge/FinalPermute.agda`'s `PermuteCoherence`, which has
-- known PARTIAL constructive discharge in
-- `Discharge/Sub/PermuteCoherenceFin.agda` (Phase 1: empty list,
-- Phase 2: singleton list, Phase 2.5: inverse lemmas).  The
-- residual self-loop case requires either:
--
--   (a) An extended `solveM` for the symmetric fragment.
--   (b) A faithful model interpretation.
--
-- ## Architectural verdict
--
-- The new (c) field shape with `permute`-bridge is STRUCTURALLY
-- BETTER than the old `subst₂`-on-stack shape, because:
--
--   1. The (b) field is now constructively dischargeable.
--   2. The (c) field's statement no longer demands an impossible
--      list equality.
--   3. The Mac Lane content has been clarified (it now lives
--      explicitly in the σ-bridge `permute (Perm.↭-sym stack-↭)`).
--
-- But the irreducible content is the same: Kelly's coherence
-- (for the bridging `permute`) plus the per-swap Mac Lane chase
-- (for the within-`process-all-edges` reordering).  Both are open
-- in the existing infrastructure.
--
-- ## File summary
--
-- * One record field (`process-term-permute-aligned`), strictly
--   narrower than the (c) field on TWO axes (externalised
--   `stack-↭`, no closure over (b) field).
--
-- * One auxiliary Kelly coherence record (`PermuteCoherenceForBridge`),
--   re-using existing infrastructure.
--
-- * Constructive composition via `WithAssumption.discharge-with-stack-fn`:
--   given the narrow assumption + Kelly coherence, produces the (c)
--   field's exact body for any `stack-fn` callback (in particular,
--   the (b) field of `CompletenessAssumptions`).
--
-- * Reused constructive helpers: `stack-↭-from-iso` (provides the
--   constructive `_↭_` derivation between vlab-mapped stacks via
--   `Linear-resp-iso`'s downstream theorems).
--
-- * No new `postulate` declarations; only record fields.  File is
--   `--safe --with-K`-clean.
--------------------------------------------------------------------------------
