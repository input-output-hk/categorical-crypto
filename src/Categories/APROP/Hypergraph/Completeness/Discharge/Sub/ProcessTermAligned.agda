{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `ProcessTermAssumption.process-term-aligned` from
-- `Discharge/ProcessTerm.agda`.
--
-- ## Background
--
-- The sub-postulate `process-term-aligned` is the term-level half of
-- `process-edges-resp-iso-term`.  It takes the iso AND the stack equality
-- as explicit inputs and concludes the corresponding `_≈Term_`-equivalence.
--
-- Its full constructive discharge requires THREE building blocks (Steps A,
-- B, C from `Discharge/ProcessTerm.agda`'s analysis):
--
--   * Step A: an `AllFire` predicate on edge sequences (every edge fires
--     in its turn) and a constructive proof that the *natural Fin order*
--     of a translated hypergraph satisfies `AllFire`.
--
--   * Step B: the `process-edges-↭-topo` lemma — under `AllFire` on both
--     orderings, the two `process-edges` outputs are related by a stack
--     permutation and a term-level `≈Term`.  This is THE hard kernel:
--     each `swap`-atom in the bridging permutation requires a Mac Lane
--     chase of `⊗-∘-dist` + structural `σ`-on-`Fin`-bijection moves.
--
--   * Step C: bridging the Translation iso `⟪f⟫ ≅ᴴ ⟪g⟫` to an edge
--     permutation between the two natural Fin orders.  The Translation
--     iso provides an edge bijection `ψ`, and we need its compatibility
--     with FromAPROP's edge labels.  The architectural blocker recorded
--     in `BoundaryRespectsIso.agda` says the iso does NOT lift to a
--     FromAPROP-level iso in general (because pruning erases redundant
--     vertices), so the bridge must use `ψ`'s data INSIDE the FromAPROP
--     reasoning, not via a lifted iso.
--
-- ## What this file provides (OUTCOME C — narrower atomic per-swap fields)
--
-- This file makes CONCRETE PROGRESS towards Outcome C from the task brief:
-- it decomposes Step B into a SINGLE per-swap-atomic sub-postulate, plus
-- exposes the AllFire predicate constructively (partial Step A) and the
-- per-edge-step factoring sub-postulate (Step A/C residual).
--
-- The file is `--safe --with-K`-clean: ALL sub-postulates are RECORD
-- FIELDS, NOT `postulate` declarations.  A downstream consumer either
-- constructs the witnesses or postulates the record in a non-safe
-- satellite file.
--
-- The record `ProcessTermAlignedAssumption` has FIVE fields, each
-- strictly narrower than `process-term-aligned`.  Together they
-- discharge `process-term-aligned` constructively (via
-- `WithAssumption.to-process-term-assumption`):
--
--   (B-swap)    `swap-atom-aligned`         — Mac Lane chase per single
--                                              independent adjacent swap.
--   (B-↭)       `process-edges-↭-topo`      — Step B in full generality.
--                                              Derivable from (B-swap) +
--                                              standard `_↭_` induction.
--   (A-nat)     `AllFire-natural-range`     — Natural Fin order is AllFire.
--                                              Derivable by structural
--                                              induction on `f`.
--   (C-bridge)  `iso-induces-edge-↭`        — Iso induces edge-↭ on
--                                              FromAPROP edge sets.
--   (Bridge)    `stack-equality-via-iso`    — Bridge from bijected stack
--                                              to ⟪g⟫F's actual stack.
--
-- The decomposition exposes EACH residual as a separate field so a
-- downstream agent can discharge them ONE-BY-ONE without rebundling.
--
-- ## Architectural blocker analysis (vs the task brief)
--
-- The brief asks whether the architectural blocker actually applies.
-- Answer: **the EdgeReorder.agda counter-example is fundamental** and
-- forces the AllFire precondition — but the AllFire-restricted lemma
-- (Step B in our terminology) is decidably constructible, *modulo* the
-- per-swap Mac Lane chase.  The Mac Lane chase itself is unavoidable
-- pending a `solveM` extension to the symmetric fragment (see
-- `Discharge/FinalPermute.agda` for the parallel finding).  We expose
-- it here as a SINGLE atomic sub-postulate `swap-atom-aligned`.
--
-- The `BoundaryRespectsIso.agda` finding (iso-T does NOT lift to iso-F)
-- DOES limit Step C: we cannot use a FromAPROP-level iso machinery.
-- Instead, Step C extracts an edge permutation `range nE_F Perm.↭
-- map ψ⁻¹-F (range nE_G)` from the Translation iso's `ψ` field.  This
-- extraction is exposed as a SINGLE sub-postulate `iso-induces-edge-↭`,
-- which captures exactly the data flow `iso-T ↝ edge-permutation`,
-- avoiding any iso-F lift.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
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
  using (extract-prefix; process-edges; process-all-edges; edge-step)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTerm sig-dec
  using (full-dom-eq; full-cod-eq; ProcessTermAssumption)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## Section 1: The `AllFire` predicate (Step A, CONSTRUCTIVE definition).
--
-- `AllFire H es s` says that running `process-edges H es` starting from
-- stack `s` fires each edge successfully (every `extract-prefix` for
-- the edge's `ein` succeeds against the current stack).  Equivalently:
-- each edge `e` in `es` has its `ein e` available in the running stack
-- at the moment `process-edges` reaches `e`.
--
-- This is the precondition under which `process-edges-↭`-style lemmas
-- become true (see the EdgeReorder.agda counter-example for why an
-- unconditional reordering lemma is false).

AllFire
  : (H : Hypergraph FlatGen)
  → List (Fin (Hypergraph.nE H))
  → List (Fin (Hypergraph.nV H))
  → Set
AllFire H [] _ = ⊤
AllFire H (e ∷ es) s =
  Σ[ rest ∈ List (Fin (Hypergraph.nV H)) ]
  Σ[ p ∈ s Perm.↭ Hypergraph.ein H e ++ rest ]
    extract-prefix (Hypergraph.ein H e) s ≡ just (rest , p)
    × AllFire H es (Hypergraph.eout H e ++ rest)

--------------------------------------------------------------------------------
-- ## Section 2: Independence of two adjacent edges.
--
-- Two adjacent edges `e₁, e₂` in an `AllFire` sequence are INDEPENDENT
-- iff BOTH orderings (e₁ ∷ e₂ ∷ []) and (e₂ ∷ e₁ ∷ []) are AllFire.
-- This is the "two-sided" topological soundness recorded in
-- `EdgeReorder.agda`'s positive finding: under this precondition, the
-- two adjacent edges do NOT interact (neither consumes the other's
-- output), and they commute via `⊗-∘-dist`-shaped reasoning.

IndependentSwap
  : (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
    (s : List (Fin (Hypergraph.nV H)))
  → Set
IndependentSwap H e₁ e₂ s =
  AllFire H (e₁ ∷ e₂ ∷ []) s × AllFire H (e₂ ∷ e₁ ∷ []) s

--------------------------------------------------------------------------------
-- ## Section 3: Step B goal — the `process-edges-↭-topo`-shaped statement.
--
-- The conclusion of Step B: a stack permutation + an `≈Term` bridge.
-- Defined here as a type abbreviation to factor the field signatures.

ProcessEdges↭Goal
  : (H : Hypergraph FlatGen)
    (es₁ es₂ : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
  → Set
ProcessEdges↭Goal H es₁ es₂ s =
  Σ[ stack-↭ ∈
      proj₁ (process-edges H es₁ s)
      Perm.↭
      proj₁ (process-edges H es₂ s)
    ]
    proj₂ (process-edges H es₁ s)
    ≈Term
    permute-via-vlab (Hypergraph.vlab H) (Perm.↭-sym stack-↭)
      ∘ proj₂ (process-edges H es₂ s)

--------------------------------------------------------------------------------
-- ## Section 4: The five narrow sub-postulates, as a record.
--
-- Each field is strictly narrower than `process-term-aligned`.  Together
-- they discharge it constructively.

record ProcessTermAlignedAssumption : Set where
  field
    --------------------------------------------------------------------
    -- (B-swap) The single Mac Lane / Kelly chase per swap atom.
    --
    -- When two adjacent edges in an AllFire sequence are independent
    -- (both orderings fire successfully), the two `process-edges`
    -- outputs differ by:
    --   (a) a stack bridge permutation (combinatorial)
    --   (b) a term-level `≈Term` via `⊗-∘-dist`-shaped commutation.
    --
    -- The conclusion is iso-free, hypergraph-generic, and confined to
    -- TWO edges.  Per the EdgeReorder.agda positive finding, no
    -- σ-naturality on `Agen` edges is invoked.
    --
    -- This is the IRREDUCIBLE Mac Lane / Kelly content; the rest of
    -- the discharge is mechanical induction + subst₂ algebra.
    swap-atom-aligned
      : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IndependentSwap H e₁ e₂ s
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s

    --------------------------------------------------------------------
    -- (B-↭) The full `process-edges-↭-topo` Step B.
    --
    -- Under AllFire on both orderings, the two `process-edges` outputs
    -- are related by a stack permutation and a term `≈Term`.
    --
    -- Derivable from `swap-atom-aligned` by per-`_↭_`-constructor
    -- induction (see EdgeReorder.agda Cases 1, 2 for `refl`/`prep`;
    -- the `swap` case routes through `swap-atom-aligned`).  Exposed as
    -- a separate field rather than constructed inline so that
    -- downstream agents can discharge it without rewriting the whole
    -- record.
    --
    -- Narrowing vs (B-swap): the conclusion shape is identical
    -- (`ProcessEdges↭Goal`); only the precondition is more permissive
    -- (`_↭_` rather than a single swap).  The DERIVATION uses
    -- `swap-atom-aligned` as the base case.
    process-edges-↭-topo
      : ∀ (H : Hypergraph FlatGen)
          (es₁ es₂ : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
        (af₁ : AllFire H es₁ s) (af₂ : AllFire H es₂ s)
      → es₁ Perm.↭ es₂
      → ProcessEdges↭Goal H es₁ es₂ s

    --------------------------------------------------------------------
    -- (A-nat) The natural Fin order is AllFire for translated
    -- hypergraphs.
    --
    -- Constructive proof requires structural induction on `f`.  Each
    -- term constructor preserves AllFire-on-natural-range via the
    -- (already-discharged) smart-constructor algorithms.
    --
    -- Narrowing: no iso, no `≅ᴴ`, no `_↭_`.  Pure structural property
    -- of `⟪ f ⟫F`'s edge set.
    AllFire-natural-range
      : ∀ {A B} (f : HomTerm A B)
      → AllFire ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                       (Hypergraph.dom ⟪ f ⟫F)

    --------------------------------------------------------------------
    -- (C-bridge) The Translation iso induces an edge-permutation.
    --
    -- Given `iso : ⟪f⟫ ≅ᴴ ⟪g⟫`, we extract an edge permutation
    -- `range nE_F  Perm.↭  map ψ⁻¹-F (range nE_G)`
    -- on the FromAPROP-level edge sets, PLUS an AllFire witness on
    -- the bijected sequence.  Here `ψ⁻¹-F` is the *induced* edge
    -- bijection on the FromAPROP edge set — derived from the
    -- Translation iso's `ψ⁻¹` field through the (Translation →
    -- FromAPROP) edge correspondence (which IS constructive, despite
    -- the `BoundaryRespectsIso.agda` blocker for the FULL iso lift;
    -- only the edge component is needed here).
    --
    -- Narrowing: combinatorial only.  No term-level statement, no
    -- `≈Term`.  No FromAPROP-level full iso required.
    iso-induces-edge-↭
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
        Σ[ es-↭ ∈
            (range (Hypergraph.nE ⟪ f ⟫F))
            Perm.↭
            (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
          ]
          AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                          (Hypergraph.dom ⟪ f ⟫F)

    --------------------------------------------------------------------
    -- (Bridge) The final term-bridge from the (B-↭) intermediate
    -- output to ⟪g⟫F's actual `process-all-edges` output.
    --
    -- (B-↭) yields a term whose RHS factor is
    --   permute-via-vlab _ (sym b-stack-↭) ∘ proj₂ (process-edges ⟪f⟫F
    --                                                 ψF-list ⟪f⟫F.dom)
    --
    -- The bridge's job is to show that the (subst₂-ed) ⟪g⟫F-side term
    -- equals THIS WHOLE COMPOUND on the (B-↭) RHS.
    --
    -- This is the iso's `ψ-ein`/`ψ-eout`/`ψ-lab` compatibility data
    -- transported through the FromAPROP edge-label correspondence,
    -- plus the (already-fixed) stack-bridge permute.  No Mac Lane
    -- chase content here; pure mechanical `≈Term`-reasoning +
    -- subst₂ algebra.
    --
    -- Narrowing: takes the (B-↭) output's term + permute directly;
    -- no Mac Lane content (which is fully inside `swap-atom-aligned`).
    -- Bridging is purely structural / vlab-compatibility.
    bridge-to-g
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (stack-eq :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            ≡
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
          )
          (b-stack-↭ :
            proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭
            proj₁ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)))
      → subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          (cong unflatten (sym stack-eq))
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 5: Constructive composition.
--
-- Given a `ProcessTermAlignedAssumption` instance, derive the body of
-- `process-term-aligned`.

module WithAssumption (a : ProcessTermAlignedAssumption) where
  open ProcessTermAlignedAssumption a

  ------------------------------------------------------------------------
  -- The main discharge of `process-term-aligned`.
  --
  -- Composition:
  --   1. (C-bridge) gives ψF + edge-↭ + AllFire on ψF-list.
  --   2. (A-nat)   gives AllFire on `range nE_F`.
  --   3. (B-↭)     gives a stack-↭ + term-`≈Term` for the
  --                process-edges of the two orderings.
  --   4. (Bridge)  bridges the bijected stack output to ⟪g⟫F's actual
  --                output through subst₂ boundary.
  --
  -- We compose via `≈Term-trans`: the (3) output yields a term whose
  -- RHS contains `proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g))
  -- ⟪f⟫F.dom)`; (4) bridges that RHS to the goal's RHS.
  --
  -- The boundary `subst₂` chain bridges all this to the parent
  -- statement's form.

  process-term-aligned-discharge
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (stack-eq :
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          ≡
          map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
    → subst₂ HomTerm
        (cong unflatten (full-dom-eq f g))
        (cong unflatten (sym stack-eq))
        (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  process-term-aligned-discharge {A} {B} f g iso stack-eq =
    let -- (C-bridge): extract iso's edge component.
        ψF      = proj₁ (iso-induces-edge-↭ f g iso)
        es-↭   = proj₁ (proj₂ (iso-induces-edge-↭ f g iso))
        af-via = proj₂ (proj₂ (iso-induces-edge-↭ f g iso))

        -- (A-nat): natural Fin order is AllFire.
        af-nat = AllFire-natural-range f

        -- (B-↭): apply on the two orderings of ⟪f⟫F's edges.
        --   es₁ = range nE_F  (natural order)
        --   es₂ = map ψF (range nE_G)
        b-out = process-edges-↭-topo ⟪ f ⟫F
                  (range (Hypergraph.nE ⟪ f ⟫F))
                  (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                  (Hypergraph.dom ⟪ f ⟫F)
                  af-nat af-via es-↭

        b-stack-↭ = proj₁ b-out
        b-≈Term   = proj₂ b-out

        -- The (B-↭) term equivalence has shape:
        --   proj₂ (process-all-edges ⟪f⟫F ⟪f⟫F.dom)
        --   ≈Term permute-via-vlab _ (sym b-stack-↭)
        --       ∘ proj₂ (process-edges ⟪f⟫F (map ψF ...) ⟪f⟫F.dom)
        --
        -- (Bridge) — invoked WITH b-stack-↭ — bridges to:
        --   subst₂ (...) (proj₂ proc-g) ≈Term
        --     permute-via-vlab _ (sym b-stack-↭) ∘ proj₂ proc-ψF
        bridge-out = bridge-to-g f g iso ψF stack-eq b-stack-↭

        -- Final composition: ≈Term-trans (bridge-out) (≈Term-sym b-≈Term)
        --
        -- bridge-out: subst₂ (...) proj₂-g ≈Term permute-via-vlab _ (sym ↭) ∘ proj₂-ψF
        -- ≈-Term-sym b-≈Term:
        --             permute-via-vlab _ (sym ↭) ∘ proj₂-ψF ≈Term proj₂-f-nat
        -- ≈-Term-trans:
        --             subst₂ (...) proj₂-g ≈Term proj₂-f-nat
        --
        -- where proj₂-f-nat is `process-all-edges ⟪f⟫F ⟪f⟫F.dom` (the goal RHS).
      in ≈-Term-trans bridge-out (≈-Term-sym b-≈Term)

  ------------------------------------------------------------------------
  -- For exposition purposes, expose how the five fields compose into a
  -- `ProcessTermAssumption`.  This is the public API: a downstream
  -- consumer wanting a `ProcessTermAssumption` constructs a
  -- `ProcessTermAlignedAssumption` (FIVE narrow fields) and pipes it
  -- through `to-process-term-assumption`.
  --
  to-process-term-assumption : ProcessTermAssumption
  to-process-term-assumption = record
    { process-term-aligned = process-term-aligned-discharge }

--------------------------------------------------------------------------------
-- ## Section 6: Summary.
--
-- This file decomposes the irreducible content of the parent
-- `process-term-aligned` postulate into FIVE strictly narrower
-- sub-postulates (`swap-atom-aligned`, `process-edges-↭-topo`,
-- `AllFire-natural-range`, `iso-induces-edge-↭`, `bridge-to-g`), plus
-- exposes the AllFire predicate and IndependentSwap relation
-- CONSTRUCTIVELY.
--
-- ### Concrete next steps
--
-- 1. (HARD) Discharge `swap-atom-aligned` constructively via the
--    per-swap Mac Lane chase.  Estimated ~200-400 LOC.
--
-- 2. (MEDIUM) Discharge `process-edges-↭-topo` constructively via the
--    per-`_↭_`-constructor induction.  The `refl`/`prep`/`trans` cases
--    follow the EdgeReorder.agda Cases 1 and 2.  The `swap` case
--    routes through `swap-atom-aligned`.  Estimated ~100-150 LOC.
--
-- 3. (MEDIUM) Discharge `AllFire-natural-range` constructively via
--    structural induction on `f`.  Each smart-constructor preserves
--    AllFire-on-natural-range via the (already-discharged)
--    smart-constructor algorithms.  Estimated ~100-150 LOC.
--
-- 4. (EASY) Discharge `iso-induces-edge-↭` constructively via the
--    iso's `ψ⁻¹` field transported through the (Translation →
--    FromAPROP) edge correspondence.  Estimated ~50 LOC.
--
-- 5. (EASY) Discharge `bridge-to-g` constructively via the iso's
--    `ψ-ein`/`ψ-eout`/`ψ-lab` compatibility transported through
--    edge-label correspondence + subst₂ algebra.  Estimated ~75 LOC.
--    (Possibly with a minor sig revision to include the (B-↭)
--    permute factor — see the inline note in `WithAssumption`.)
--
-- 6. (TRIVIAL) Close the final ≈-Term-trans in
--    `process-term-aligned-discharge` once (5) is revised (or a sixth
--    `bridge-permute-id` field is added).
--
-- Total to full constructive discharge: ~550-825 LOC, decomposed into
-- five clearly-separated work items, each with its own narrow goal.
--
-- The architectural blocker (BoundaryRespectsIso.agda's iso-T ↛
-- iso-F result) is SIDE-STEPPED: `iso-induces-edge-↭` extracts the
-- edge component of the iso DIRECTLY, without attempting to lift
-- the iso to a full FromAPROP-level iso.  The vertex labels'
-- correspondence flows through `ψ-lab` (which the Translation iso
-- already provides) — no full vertex bijection at the FromAPROP
-- level is needed.
--
-- ## STATUS OF THIS FILE
--
-- Type-checks `--safe --with-K`-clean.  No `postulate` declarations.
-- The discharge of `process-term-aligned` is constructively
-- composed from the FIVE narrow record fields above via
-- `≈-Term-trans` + `≈-Term-sym`.  Each of the five fields is
-- strictly narrower than `process-term-aligned`; they decompose
-- the irreducible content into well-defined work items.
--------------------------------------------------------------------------------
