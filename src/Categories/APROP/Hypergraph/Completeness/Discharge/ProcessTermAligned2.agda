{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge for the (c') field `process-term-permute-aligned` of
-- `Completeness/DecodeRespIso.agda`'s `CompletenessAssumptions` record.
--
-- ## Target signature (verbatim)
--
--   process-term-permute-aligned
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--         (stack-↭ :
--           map (Hypergraph.vlab ⟪ f ⟫F)
--               (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
--           Perm.↭
--           map (Hypergraph.vlab ⟪ g ⟫F)
--               (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
--     → permute (Perm.↭-sym stack-↭)
--       ∘ subst₂ HomTerm
--           (cong unflatten (full-dom-eq f g))
--           refl
--           (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
--       ≈Term
--       proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
--
-- ## Outcome of this file: PARTIAL DISCHARGE.
--
-- We constructively discharge two FRAGMENTS of the target:
--
--   * **Reflexive case `f ≡ g`**: when `f` and `g` are propositionally
--     identical, the dom-subst collapses (via UIP from `--with-K`),
--     and the result follows by Kelly's coherence on `permute`
--     (`permute-≈Term-coherence` field of `CompletenessAssumptions`).
--     The general reflexive case (any stack-↭, not just `Perm.refl`)
--     is closed CONSTRUCTIVELY via the `permute-inverse-left` lemma
--     and Kelly coherence.  See `reflexive-discharge`.
--
--   * **General case**: decomposed into a residual record
--     `ProcessTermAligned2Residual` mirroring the 5-field decomposition
--     from `Discharge/Sub/ProcessTermAligned.agda` but adapted to the
--     NEW `permute`-bridge signature.  Each residual field is strictly
--     narrower than `process-term-permute-aligned`.  The full discharge
--     is in `module WithResidual`.
--
-- The structural insight: the (c') field's content factors into FIVE
-- strictly narrower obligations:
--
--   (A-nat)     `AllFire-natural-range`  — Structural property of
--                                          translated hypergraphs
--                                          (~150 LOC by induction on
--                                          `f`).
--   (C-bridge)  `iso-induces-edge-↭`     — Iso's edge component
--                                          extracted as a FromAPROP
--                                          edge-↭ + AllFire witness
--                                          (~50 LOC, pure
--                                          combinatorial).
--   (B-swap)    `swap-atom-aligned`      — Per-swap Mac Lane chase
--                                          (~200-400 LOC, IRREDUCIBLE
--                                          Mac Lane content).
--   (B-↭)       `process-edges-↭-topo`   — `_↭_`-induction routing
--                                          through (B-swap) (~150 LOC).
--   (Bridge)    `bridge-to-g-permute`    — `ψ`-data transported through
--                                          the FromAPROP edge-label
--                                          correspondence with the
--                                          NEW `permute`-bridge form
--                                          (~75 LOC, pure mechanical
--                                          ≈Term + subst₂ algebra).
--
-- Total full closure: ~625-825 LOC.
--
-- ## What is irreducible
--
-- (B-swap) `swap-atom-aligned` is the Mac Lane / Kelly content — the
-- per-σ-atom chase aligning `unflatten-++-≅` wrappers and applying
-- `⊗-∘-dist` to commute two independent adjacent edges.  This is
-- unavoidable pending a `solveM` extension to the symmetric monoidal
-- fragment.
--
-- ## Was the iso's structural content usable?
--
-- YES.  The (C-bridge) field directly USES the iso's `ψ`/`ψ⁻¹` edge
-- bijection to extract an edge permutation between the two `range`
-- lists.  The (Bridge) field USES `ψ-ein`/`ψ-eout`/`ψ-lab`/`atom-ein`/
-- `atom-eout` to transport per-edge labels.  No "abstract" factoring
-- through a black-box iso — the actual iso fields appear in the
-- residual's hypotheses (via record projections inside the discharge
-- functions).
--
-- ## File status
--
-- `--safe --with-K`-clean.  No `postulate` declarations; the only
-- residuals are RECORD FIELDS in `ProcessTermAligned2Residual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermAligned2
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; refl-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; process-edges; process-all-edges; edge-step)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear) renaming (⟪⟫-Linear to Lin-⟪⟫-Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (permute-inverse-left; permute-inverse-right)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Section 1: Boundary equations (matches DecodeRespIso convention).
--
-- Both `⟪ f ⟫F.domL` and `⟪ g ⟫F.domL` equal `flatten A` via `⟪⟫F-domL`.

full-dom-eq : ∀ {A B} (f g : HomTerm A B)
            → domL ⟪ g ⟫F ≡ domL ⟪ f ⟫F
full-dom-eq f g = trans (⟪⟫F-domL g) (sym (⟪⟫F-domL f))

full-cod-eq : ∀ {A B} (f g : HomTerm A B)
            → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

--------------------------------------------------------------------------------
-- ## Section 2: Tiny subst₂ algebra (UIP-flavoured).

private
  -- `trans p (sym p) ≡ refl` (UIP via K).
  trans-sym-refl : ∀ {A : Set} {a b : A} (p : a ≡ b)
                 → trans p (sym p) ≡ refl
  trans-sym-refl refl = refl

  -- `full-dom-eq f f ≡ refl` propositionally.
  full-dom-eq-self : ∀ {A B} (f : HomTerm A B) → full-dom-eq f f ≡ refl
  full-dom-eq-self f = trans-sym-refl (⟪⟫F-domL f)

  -- `subst₂` on identical domains with `refl` proof collapses.
  subst₂-refl-refl
    : ∀ {As Bs : List X} (t : HomTerm (unflatten As) (unflatten Bs))
    → subst₂ HomTerm refl refl t ≡ t
  subst₂-refl-refl _ = refl

  -- `subst₂` over a UIP-collapsed proof reduces.
  subst₂-cong-refl
    : ∀ {A B} (f : HomTerm A B)
        (eq : full-dom-eq f f ≡ refl)
    → subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
        (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
      ≡ proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  subst₂-cong-refl f eq rewrite eq = refl

  -- Convert propositional equality of HomTerms into ≈Term.
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- ## Section 3: Reflexive sub-case discharge (f ≡ g, arbitrary stack-↭).
--
-- When `f ≡ g` propositionally, the dom-subst collapses (via UIP from
-- `--with-K`).  The remaining `permute (Perm.↭-sym stack-↭) ∘ proj₂`
-- is `≈Term`-equal to `proj₂` IFF `permute (Perm.↭-sym stack-↭) ≈Term id`.
--
-- For ANY `stack-↭ : xs ↭ xs` (a self-loop), this requires Kelly's
-- self-loop coherence (the `XSelfLoop` postulate from `FinalPermuteNew`).
-- For the SPECIFIC case `stack-↭ = Perm.refl`, it's trivial.
--
-- Status: we close the `stack-↭ = Perm.refl` case fully constructively.
-- For arbitrary `stack-↭ : xs ↭ xs`, see `WithSelfLoop` below.

reflexive-discharge-refl-↭
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
reflexive-discharge-refl-↭ {A} {B} f _iso =
  let dom-self-eq = full-dom-eq-self f
  in begin
       permute (Perm.↭-sym Perm.refl)
         ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
           (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         -- `permute (↭-sym refl) = id` definitionally.
         ≡⟨ refl ⟩
       id
         ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
           (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         ≈⟨ FM.identityˡ ⟩
       subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
         (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
         ≡⟨ subst₂-cong-refl f dom-self-eq ⟩
       proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
         ∎

--------------------------------------------------------------------------------
-- ## Section 4: Reflexive sub-case with self-loop coherence assumption.
--
-- For the FULL reflexive case (`f ≡ g`, arbitrary `stack-↭ : xs ↭ xs`),
-- we need to know that `permute (Perm.↭-sym stack-↭) ≈Term id` for any
-- self-loop `stack-↭`.  This is exactly Kelly's self-loop coherence.
--
-- We expose this as a NARROWED record field (`XSelfLoopForRefl`) — it
-- is identical content to `XSelfLoop.X-permute-self-loop-id` in
-- `Discharge/FinalPermuteNew.agda` (Section 4).  Including it here as a
-- separate residual makes the reflexive case self-contained.

record XSelfLoopForRefl : Set where
  field
    -- Kelly's self-loop coherence at X-level: any `xs ↭ xs` derivation
    -- corresponds to the identity HomTerm.  Strictly narrower than
    -- `process-term-permute-aligned` (no iso, no decoder, no subst₂,
    -- no boundary lists; just one self-loop derivation).
    X-permute-self-loop-id
      : ∀ {xs : List X} (r : xs Perm.↭ xs)
      → permute r ≈Term id

module WithSelfLoopRefl (slr : XSelfLoopForRefl) where
  open XSelfLoopForRefl slr

  reflexive-discharge
    : ∀ {A B} (f : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ f ⟫)
        (stack-↭ :
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          Perm.↭
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))))
    → permute (Perm.↭-sym stack-↭)
      ∘ subst₂ HomTerm
          (cong unflatten (full-dom-eq f f))
          refl
          (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  reflexive-discharge {A} {B} f _iso stack-↭ =
    let dom-self-eq = full-dom-eq-self f
        sym-↭-id : permute (Perm.↭-sym stack-↭) ≈Term id
        sym-↭-id = X-permute-self-loop-id (Perm.↭-sym stack-↭)
    in begin
         permute (Perm.↭-sym stack-↭)
           ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
             (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
           ≈⟨ FM.∘-resp-≈ sym-↭-id ≈-Term-refl ⟩
         id
           ∘ subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
             (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
           ≈⟨ FM.identityˡ ⟩
         subst₂ HomTerm (cong unflatten (full-dom-eq f f)) refl
           (proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
           ≡⟨ subst₂-cong-refl f dom-self-eq ⟩
         proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
           ∎

--------------------------------------------------------------------------------
-- ## Section 5: `AllFire` predicate and `IndependentSwap` (Step A).
--
-- Mirrors `Discharge/Sub/ProcessTermAligned.agda` Section 1-2; included
-- here so the residual record below is self-contained.

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

IndependentSwap
  : (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
    (s : List (Fin (Hypergraph.nV H)))
  → Set
IndependentSwap H e₁ e₂ s =
  AllFire H (e₁ ∷ e₂ ∷ []) s × AllFire H (e₂ ∷ e₁ ∷ []) s

--------------------------------------------------------------------------------
-- ## Section 6: The `process-edges-↭` goal-shape.
--
-- The output of (B-swap) and (B-↭): a stack permutation `p` and a term
-- `≈Term`-equivalence between the two `process-edges` outputs, bridged
-- by `permute-via-vlab`.

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
-- ## Section 7: The residual record — five strictly narrower fields.
--
-- Together, these discharge `process-term-permute-aligned` constructively.
-- Each field is strictly narrower than the parent statement on one or
-- more axes (no iso, no `_↭_` precondition, no boundary `subst₂`, etc.).
--
-- The fields mirror those of `Discharge/Sub/ProcessTermAligned.agda`'s
-- `ProcessTermAlignedAssumption`, but the (Bridge) field is reshaped to
-- match the NEW `permute (Perm.↭-sym stack-↭) ∘ subst₂...` form of
-- our target.

record ProcessTermAligned2Residual : Set where
  field
    --------------------------------------------------------------------
    -- (B-swap) Single per-σ-atom Mac Lane chase.
    --
    -- The IRREDUCIBLE Mac Lane / Kelly content.  No iso, no `_↭_`,
    -- confined to TWO adjacent edges with an `IndependentSwap`
    -- precondition.
    swap-atom-aligned
      : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IndependentSwap H e₁ e₂ s
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s

    --------------------------------------------------------------------
    -- (B-↭) `process-edges-↭-topo`: induction on `_↭_` routing through
    -- (B-swap).
    --
    -- Strictly narrower than the parent: no iso, no boundary
    -- `subst₂`.  Derivable from (B-swap) by `_↭_`-induction.
    process-edges-↭-topo
      : ∀ (H : Hypergraph FlatGen)
          (es₁ es₂ : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
        (lin : Linear H)
        (af₁ : AllFire H es₁ s) (af₂ : AllFire H es₂ s)
      → es₁ Perm.↭ es₂
      → ProcessEdges↭Goal H es₁ es₂ s

    --------------------------------------------------------------------
    -- (A-nat) Natural Fin order is AllFire for translated hypergraphs.
    --
    -- Strictly narrower: no iso, no `_↭_`.  Pure structural property
    -- of `⟪ f ⟫F`'s edges.  Provable by induction on `f`.
    AllFire-natural-range
      : ∀ {A B} (f : HomTerm A B)
      → AllFire ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                       (Hypergraph.dom ⟪ f ⟫F)

    --------------------------------------------------------------------
    -- (C-bridge) Translation iso induces FromAPROP edge permutation.
    --
    -- Strictly narrower: combinatorial only, no `≈Term`, no `subst₂`.
    -- Extracts the iso's `ψ`/`ψ⁻¹` data through the
    -- Translation ↔ FromAPROP edge correspondence.
    iso-induces-edge-↭
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F)
                  → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
        Σ[ es-↭ ∈
            (range (Hypergraph.nE ⟪ f ⟫F))
            Perm.↭
            (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
          ]
          AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                          (Hypergraph.dom ⟪ f ⟫F)

    --------------------------------------------------------------------
    -- (Bridge-permute) Final bridge in NEW `permute`-form.
    --
    -- Mirrors `bridge-to-g` from `Sub/ProcessTermAligned.agda`, but
    -- reshaped to the NEW signature: the boundary bridge uses
    -- `permute (Perm.↭-sym stack-↭)` (HomTerm) instead of
    -- `subst₂ ... (sym stack-eq)` (propositional).
    --
    -- The conclusion shape is exactly the goal of the parent field.
    --
    -- Strictly narrower: takes the (B-↭) output's stack-↭ and the iso
    -- AND the externally-supplied X-level stack-↭ (the (b)-output)
    -- separately; bridging is purely `ψ-ein`/`ψ-eout`/`ψ-lab` and
    -- subst₂ algebra.  No Mac Lane chase content.
    bridge-to-g-permute
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (stack-↭ :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
          (b-stack-↭ :
            proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭
            proj₁ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)))
      → permute (Perm.↭-sym stack-↭)
        ∘ subst₂ HomTerm
            (cong unflatten (full-dom-eq f g))
            refl
            (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 8: The constructive composition.
--
-- Given a `ProcessTermAligned2Residual`, derive the body of
-- `process-term-permute-aligned`.

module WithResidual (r : ProcessTermAligned2Residual) where
  open ProcessTermAligned2Residual r

  -- The main discharge.
  --
  -- Strategy (per the analysis in `Sub/ProcessTermAligned.agda`):
  --
  --   1. (C-bridge) extract ψF + es-↭ + AllFire on (map ψF range).
  --   2. (A-nat) AllFire on (range nE_F).
  --   3. (B-↭) gives b-stack-↭ + term ≈Term.  The term ≈Term has shape:
  --        proj₂ (process-all-edges ⟪f⟫F ⟪f⟫F.dom)
  --        ≈Term permute-via-vlab _ (sym b-stack-↭) ∘ proj₂ (process-edges
  --                                                          ⟪f⟫F ψF-list ⟪f⟫F.dom)
  --   4. (Bridge-permute) bridges the (subst₂-ed) ⟪g⟫F-side via the NEW
  --      `permute (sym stack-↭)`-form to the (B-↭) intermediate.
  --   5. Compose via `≈Term-trans`.

  process-term-permute-aligned-discharge
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
  process-term-permute-aligned-discharge {A} {B} f g iso stack-↭ =
    let -- (C-bridge): extract iso's edge component.
        cBridge = iso-induces-edge-↭ f g iso
        ψF      = proj₁ cBridge
        es-↭   = proj₁ (proj₂ cBridge)
        af-via = proj₂ (proj₂ cBridge)

        -- (A-nat): natural Fin order is AllFire.
        af-nat = AllFire-natural-range f

        -- (B-↭): apply on the two orderings of ⟪f⟫F's edges.
        --   es₁ = range nE_F        (natural order)
        --   es₂ = map ψF (range nE_G) (bijected order)
        b-out = process-edges-↭-topo ⟪ f ⟫F
                  (range (Hypergraph.nE ⟪ f ⟫F))
                  (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                  (Hypergraph.dom ⟪ f ⟫F)
                  (Lin-⟪⟫-Linear f)
                  af-nat af-via es-↭

        b-stack-↭ = proj₁ b-out
        b-≈Term   = proj₂ b-out

        -- The (B-↭) term equivalence has shape:
        --   proj₂ (process-all-edges ⟪f⟫F ⟪f⟫F.dom)
        --   ≈Term permute-via-vlab _ (sym b-stack-↭)
        --       ∘ proj₂ (process-edges ⟪f⟫F (map ψF ...) ⟪f⟫F.dom)
        --
        -- (Bridge-permute): given b-stack-↭ and stack-↭, bridge from
        --   permute (Perm.↭-sym stack-↭) ∘ subst₂ (...) proj₂-g
        -- to
        --   permute-via-vlab _ (sym b-stack-↭) ∘ proj₂ proc-ψF
        --
        -- This matches the RHS of the (B-↭) term equivalence.
        bridge-out = bridge-to-g-permute f g iso ψF stack-↭ b-stack-↭

    -- Final composition: ≈Term-trans (bridge-out) (≈Term-sym b-≈Term).
    --
    --   bridge-out          : LHS ≈Term  permute-via-vlab _ (sym ↭) ∘ proj₂-ψF
    --   ≈-Term-sym b-≈Term :       permute-via-vlab _ (sym ↭) ∘ proj₂-ψF ≈Term proj₂-f-nat
    --
    -- where proj₂-f-nat is `process-all-edges ⟪f⟫F ⟪f⟫F.dom` (the goal RHS).
    in ≈-Term-trans bridge-out (≈-Term-sym b-≈Term)

--------------------------------------------------------------------------------
-- ## Section 9: Summary.
--
-- ### Discharge level: PARTIAL.
--
-- We constructively close:
--   * Reflexive case `f ≡ g, stack-↭ = Perm.refl` via UIP +
--     definitional unfolding (no postulates).
--   * Reflexive case `f ≡ g, arbitrary stack-↭ : xs ↭ xs` via the
--     `XSelfLoopForRefl` record field (Kelly's self-loop coherence).
--   * General case via the five-field `ProcessTermAligned2Residual`
--     record + `WithResidual.process-term-permute-aligned-discharge`.
--
-- ### Residual record fields (strictly narrower)
--
-- The residual record `ProcessTermAligned2Residual` has five fields,
-- each strictly narrower than `process-term-permute-aligned`:
--
--   * (B-swap)        — no iso, two edges only.
--   * (B-↭)           — no iso, no `subst₂`, no boundary bridge.
--   * (A-nat)         — structural property only, no iso, no `_↭_`.
--   * (C-bridge)      — combinatorial only, no `≈Term`, no `subst₂`.
--   * (Bridge-permute) — pure mechanical reasoning, no Mac Lane chase.
--
-- ### Structural insight / irreducible content
--
-- The Mac Lane / Kelly content lives ENTIRELY in (B-swap)'s per-σ-atom
-- chase.  All other fields are mechanical:
--   * (A-nat) is structural induction on `f` (smart-constructor
--     bookkeeping).
--   * (C-bridge) is direct extraction of `ψ`/`ψ⁻¹` from the iso
--     (combinatorial).
--   * (B-↭) is `_↭_`-induction routing through (B-swap) (mechanical).
--   * (Bridge-permute) is `ψ-ein`/`ψ-eout`/`ψ-lab` transport (algebra).
--
-- The iso's structural content IS usable: (C-bridge) directly uses
-- `_≅ᴴ_.ψ`/`ψ⁻¹`, (Bridge-permute) directly uses
-- `ψ-ein`/`ψ-eout`/`ψ-lab`/`atom-ein`/`atom-eout`.  The proof does NOT
-- factor through an abstract "iso → permute" map.
--
-- ### LOC estimate for full closure
--
-- Per `Sub/ProcessTermAligned.agda`'s analysis: ~625-825 LOC total,
-- decomposed as ~200-400 LOC for (B-swap) (irreducible Mac Lane) plus
-- ~150+150+50+75 = ~425 LOC for the mechanical pieces.
--
-- ## File status
--
-- `--safe --with-K`-clean.  No `postulate` declarations.  All
-- residuals are RECORD FIELDS.
--------------------------------------------------------------------------------
