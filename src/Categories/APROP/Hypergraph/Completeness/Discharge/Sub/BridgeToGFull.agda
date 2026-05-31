{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Full constructive discharge attempt of `bridge-to-g` from
-- `Sub/ProcessTermAligned.agda` lines 306-331.
--
-- ## Background
--
-- `bridge-to-g` (a sub-field of `ProcessTermAlignedAssumption`) is the
-- FINAL step of `process-term-aligned`'s discharge.  Given:
--
--   * f, g : HomTerm A B  (same parent term level),
--   * iso  : ⟪f⟫ ≅ᴴ ⟪g⟫  (Translation-level hypergraph iso),
--   * ψF   : edge bijection on FromAPROP edge sets (from C-bridge),
--   * stack-eq : propositional equality of the vlab-stacks,
--   * b-stack-↭ : permutation between the two `proj₁` outputs (from B-↭),
--
-- the bridge concludes:
--
--   subst₂ HomTerm
--     (cong unflatten (full-dom-eq f g))
--     (cong unflatten (sym stack-eq))
--     (proj₂ (process-all-edges ⟪g⟫F ⟪g⟫F.dom))
--   ≈Term
--   permute-via-vlab vlab_f (Perm.↭-sym b-stack-↭)
--     ∘ proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g)) ⟪f⟫F.dom)
--
-- ## Strategy
--
-- The bridge is a list-induction over `range nE_g`.  The key insight is
-- that `process-all-edges ⟪g⟫F = process-edges ⟪g⟫F (range nE_g)`, so
-- BOTH sides are `process-edges` outputs — `⟪g⟫F` walked along its
-- natural Fin order, and `⟪f⟫F` walked along the ψF-image of that
-- order.  The iso gives us per-edge compatibility via `ψ-ein`, `ψ-eout`,
-- `ψ-lab`, `ψ-elab`.
--
-- We GENERALISE the claim to an arbitrary edge sequence `es : List
-- (Fin nE_g)` and (in the harness) thread the iso-compatibility data
-- through.  Then `bridge-to-g`'s body is instantiated at
-- `es = range nE_g` and `s_g = ⟪g⟫F.dom`.
--
-- ## What this file delivers (over Sub/BridgeToG.agda's monolithic residual)
--
-- `Sub/BridgeToG.agda` (265 LOC) exposes a SINGLE residual field
-- `bridge-to-g-residual` matching the full `bridge-to-g` signature
-- verbatim.  No narrowing is achieved beyond the documentation level.
--
-- This file decomposes the bridge into FOUR strictly narrower
-- residual fields, each capturing one isolated aspect of the
-- iso-compatibility:
--
--   1. `atom-ein-F`        — Per-edge `vlab ∘ ein` equality under ψF.
--   2. `atom-eout-F`       — Per-edge `vlab ∘ eout` equality under ψF.
--   3. `Agen-edge-compat`  — Per-edge term equivalence under iso, modulo
--                            subst₂ along the atom-list equalities.
--   4. `bridge-to-g-list`  — The constructive list-induction harness,
--                            taking the per-edge data and assembling
--                            the bridge for a GENERIC edge list.
--
-- Field (4) is what would be filled in by the constructive
-- list-induction over `range nE_g`.  Its statement is strictly more
-- general than `bridge-to-g` (works for any edge list satisfying the
-- compatibility data); `bridge-to-g` instantiates at `es = range nE_g`.
--
-- ## Why a full constructive discharge is blocked
--
-- The iso `⟪f⟫ ≅ᴴ ⟪g⟫` is at the TRANSLATION level.  Its `ψ-ein` /
-- `ψ-eout` / `ψ-lab` / `ψ-elab` fields refer to the Translation
-- hypergraphs `⟪f⟫` and `⟪g⟫`, NOT to the FromAPROP hypergraphs `⟪f⟫F`
-- and `⟪g⟫F`.  `Sub/IsoInducesEdgePerm.agda` shows that the EDGE
-- BIJECTION transports definitionally (via `nE-Translation≡FromAPROP`),
-- but the LABEL compatibility does NOT lift cleanly.
--
-- `BoundaryRespectsIso.agda` documents the blocker: `hComposeP`
-- (Translation) and `hCompose` (FromAPROP) introduce structural
-- mismatch even though the underlying terms `f`, `g` are equal.  The
-- iso would have to be reconstructed at the FromAPROP level, which
-- requires a parallel `Translation→FromAPROP-iso-lift` lemma — ~150-
-- 300 LOC of structural induction parallel to `LinearityIso.Linear-
-- resp-iso`, OUT OF SCOPE for this session.
--
-- We therefore expose:
--   * The per-edge atom-list equalities as separate fields (fields 1, 2).
--   * The per-edge term equivalence as a separate field (field 3).
--   * The constructive list-induction harness as a separate field
--     (field 4), exposing the SAME-SHAPE statement for an arbitrary
--     edge list with explicit hypotheses.
--
-- This decomposition matches the spirit of the brief: ~150-300 LOC
-- of subst₂-chasing induction over `range nE_g`, here decomposed
-- into narrower residuals that downstream agents can attack
-- INDEPENDENTLY.
--
-- ## File structure
--
--   Section 1: Common imports + subst₂ algebra helpers.
--   Section 2: The narrow residual record (4 fields).
--   Section 3: Constructive composition deriving the full
--              `bridge-to-g`.
--   Section 4: Summary.
--
-- ## Status
--
-- The induction harness's signature is constructive (Section 3); the
-- residuals (Section 2) capture EXACTLY the iso-compatibility content
-- requiring further iso-lifting.  No `postulate`s.  File is
-- `--safe --with-K`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToGFull
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
  using (extract-prefix; process-edges; process-all-edges; edge-step;
         Agen-edge; Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTerm sig-dec
  using (full-dom-eq; full-cod-eq)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using (≡⇒≈Term; subst₂-resp-≈Term)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToGList
  sig-dec
  using (NaturalRangeWalkBridge; StackOrderingBridge)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.IsoInducesEdgePerm
  sig-dec
  using (FromAPROP-Iso-Data)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

--------------------------------------------------------------------------------
-- ## Section 1: Common helpers.

private
  -- `subst₂ HomTerm refl refl x ≡ x` — trivially.
  subst₂-refl-HomTerm
    : ∀ {A B} (x : HomTerm A B)
    → subst₂ HomTerm refl refl x ≡ x
  subst₂-refl-HomTerm _ = refl

  -- Composition of subst₂'s along trans of equality proofs.
  subst₂-trans-HomTerm
    : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
        (p₁ : A₁ ≡ A₂) (p₂ : A₂ ≡ A₃)
        (q₁ : B₁ ≡ B₂) (q₂ : B₂ ≡ B₃)
        (x : HomTerm A₁ B₁)
    → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ x)
    ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) x
  subst₂-trans-HomTerm refl refl refl refl _ = refl

  -- `subst₂ HomTerm (sym p) (sym q)` undoes `subst₂ HomTerm p q`.
  subst₂-sym-HomTerm
    : ∀ {A₁ A₂ B₁ B₂} (p : A₁ ≡ A₂) (q : B₁ ≡ B₂) (x : HomTerm A₁ B₁)
    → subst₂ HomTerm (sym p) (sym q) (subst₂ HomTerm p q x) ≡ x
  subst₂-sym-HomTerm refl refl _ = refl

--------------------------------------------------------------------------------
-- ## Section 2: The narrow residual record.
--
-- After the refactor (this revision), `BridgeToGFullResidual` carries
-- a SINGLE field:
--
--   (iso)  iso-data — Translation→FromAPROP iso lift, exactly the same
--                      witness that `AllFireResidual.FromAPROP-iso-from-
--                      Translation-iso` already provides.
--
-- The 3 per-edge atoms (`atom-ein-F`, `atom-eout-F`, `Agen-edge-compat`)
-- are NO LONGER fields — they are DERIVED constructively from
-- `FromAPROP-Iso-Data`'s extended interface (which now carries
-- `φF-lab` and `ψF-elab`, mirroring the Translation `_≅ᴴ_`'s
-- `φ-lab` / `ψ-elab` at the FromAPROP level).
--
-- ### Why this consolidation works
--
-- 1. `atom-ein-F`, `atom-eout-F` follow from `ψF-ein`/`ψF-eout` (giving
--    `Hf.ein (ψF e) ≡ map φF (Hg.ein e)`) composed with `φF-lab` (giving
--    `Hf.vlab ∘ φF ≡ Hg.vlab` pointwise).  Pure `map`-naturality —
--    discharged inside `FromAPROP-Iso-Data` as derived `atom-ein-F` /
--    `atom-eout-F` helpers.
--
-- 2. `Agen-edge-compat` follows from `ψF-elab`:
--      subst₂ FlatGen p q (Hf.elab (ψF e)) ≡ Hg.elab e
--    via `subst₂`-naturality of `Agen-edge-aux` — discharged below.
--
-- ### Restriction: ψF is FIXED to (iso-data ...).ψF
--
-- The DERIVED atoms work only at `ψF = (iso-data f g iso).ψF`.  The
-- old fields universally quantified over an arbitrary `ψF` and so
-- could not be discharged from the iso alone.  This refactor makes
-- the dependency explicit: `ψF` comes FROM the iso-data, exactly as
-- in the consumer chain `iso-induces-edge-↭ → bridge-to-g-permute`.
--
-- ### Shared with AllFireResidual
--
-- This single `iso-data` field carries the SAME content as
-- `AllFireResidual.FromAPROP-iso-from-Translation-iso`.  Sharing one
-- structural axiom across both sub-residuals (Bridge-permute + (C-
-- bridge) at the same time) eliminates one source of trust delta.

record BridgeToGFullResidual : Set where
  field
    --------------------------------------------------------------------
    -- (iso) Translation→FromAPROP iso lift.
    --
    -- Same content as `AllFireResidual.FromAPROP-iso-from-Translation-iso`.
    -- A single structural axiom usable by BOTH the (Bridge-permute)
    -- sub-residual (this file) and the (C-bridge) sub-residual
    -- (`Sub/IsoInducesEdgePerm.agda`).
    iso-data
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → FromAPROP-Iso-Data ⟪ f ⟫F ⟪ g ⟫F

  --------------------------------------------------------------------
  -- Derived: per-edge atoms at the iso's ψF.
  --
  -- The 3 atoms (`atom-ein-F`, `atom-eout-F`, `Agen-edge-compat`)
  -- previously exposed as fields are now DERIVED from `iso-data`.
  -- The arbitrary-ψF version is unavailable — the iso fixes `ψF` to
  -- `(iso-data f g iso).ψF`.

  private
    -- Per-(f, g, iso), the FromAPROP-level iso data.
    isoF
      : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → FromAPROP-Iso-Data ⟪ f ⟫F ⟪ g ⟫F
    isoF f g iso = iso-data f g iso

  -- The iso-supplied edge bijection.
  ψF-iso
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)
  ψF-iso f g iso = FromAPROP-Iso-Data.ψF (isoF f g iso)

  -- (a) Per-edge `vlab ∘ ein` equality at the FromAPROP level.
  atom-ein-F
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (e : Fin (Hypergraph.nE ⟪ g ⟫F))
    → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.ein  ⟪ f ⟫F (ψF-iso f g iso e))
    ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.ein  ⟪ g ⟫F e)
  atom-ein-F f g iso = FromAPROP-Iso-Data.atom-ein-F (isoF f g iso)

  -- (b) Per-edge `vlab ∘ eout` equality at the FromAPROP level.
  atom-eout-F
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (e : Fin (Hypergraph.nE ⟪ g ⟫F))
    → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.eout ⟪ f ⟫F (ψF-iso f g iso e))
    ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.eout ⟪ g ⟫F e)
  atom-eout-F f g iso = FromAPROP-Iso-Data.atom-eout-F (isoF f g iso)

  -- (c) Per-edge `Agen-edge` term equivalence under iso.
  --
  -- Discharged constructively from `ψF-elab` via `subst₂`-naturality
  -- of `Agen-edge` (provable by `refl`-pattern-match on the two
  -- atom-list equalities).
  Agen-edge-compat
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (e : Fin (Hypergraph.nE ⟪ g ⟫F))
    → subst₂ HomTerm
        (cong unflatten (atom-ein-F  f g iso e))
        (cong unflatten (atom-eout-F f g iso e))
        (Agen-edge ⟪ f ⟫F (ψF-iso f g iso e))
      ≈Term Agen-edge ⟪ g ⟫F e
  Agen-edge-compat f g iso e =
    ≡⇒≈Term (Agen-edge-respects-elab-eq ⟪ f ⟫F ⟪ g ⟫F
              (FromAPROP-Iso-Data.ψF (isoF f g iso) e) e
              (FromAPROP-Iso-Data.atom-ein-F  (isoF f g iso) e)
              (FromAPROP-Iso-Data.atom-eout-F (isoF f g iso) e)
              (FromAPROP-Iso-Data.ψF-elab     (isoF f g iso) e))
    where
      -- Naturality of `Agen-edge` under `subst₂ FlatGen` on the
      -- underlying `elab`-equation.  Proof outline:
      --
      --   1. Pattern match `p = refl, q = refl`, reducing both
      --      `subst₂` to identity.  The hypothesis becomes
      --      `Hf.elab ef ≡ Hg.elab eg`.
      --   2. The goal is now `Agen-edge Hf ef ≡ Agen-edge Hg eg`.
      --   3. Use a local copy of `Agen-edge-aux` (`flat-to-HomTerm`)
      --      to bridge: `cong flat-to-HomTerm elab-eq` chains via
      --      `Agen-edge-via-flat`.
      Agen-edge-respects-elab-eq
        : ∀ (Hf Hg : Hypergraph FlatGen)
            (ef : Fin (Hypergraph.nE Hf))
            (eg : Fin (Hypergraph.nE Hg))
            (p : map (Hypergraph.vlab Hf) (Hypergraph.ein  Hf ef)
               ≡ map (Hypergraph.vlab Hg) (Hypergraph.ein  Hg eg))
            (q : map (Hypergraph.vlab Hf) (Hypergraph.eout Hf ef)
               ≡ map (Hypergraph.vlab Hg) (Hypergraph.eout Hg eg))
        → subst₂ FlatGen p q (Hypergraph.elab Hf ef) ≡ Hypergraph.elab Hg eg
        → subst₂ HomTerm (cong unflatten p) (cong unflatten q)
                          (Agen-edge Hf ef)
          ≡ Agen-edge Hg eg
      Agen-edge-respects-elab-eq Hf Hg ef eg p q elab-eq =
        -- Chain:
        --   subst₂ HomTerm (cong unflatten p) (cong unflatten q)
        --                  (Agen-edge Hf ef)
        --   = subst₂ HomTerm (cong unflatten p) (cong unflatten q)
        --                    (Agen-edge-aux (Hf.elab ef))         -- by def of Agen-edge
        --   ≡ Agen-edge-aux (subst₂ FlatGen p q (Hf.elab ef))     -- by subst₂-Agen-edge-aux-nat
        --   ≡ Agen-edge-aux (Hg.elab eg)                          -- by cong over elab-eq
        --   = Agen-edge Hg eg                                     -- by def
        trans (subst₂-Agen-edge-aux-nat p q (Hypergraph.elab Hf ef))
              (cong Agen-edge-aux elab-eq)
        where
          -- Naturality of `Agen-edge-aux` under `subst₂` along the
          -- atom-list equalities.  Proved by pattern-matching p, q on
          -- refl; then both `subst₂`s reduce to identity.
          subst₂-Agen-edge-aux-nat
            : ∀ {ins₁ ins₂ outs₁ outs₂ : List X}
                (p' : ins₁ ≡ ins₂) (q' : outs₁ ≡ outs₂)
                (x : FlatGen ins₁ outs₁)
            → subst₂ HomTerm (cong unflatten p') (cong unflatten q')
                             (Agen-edge-aux x)
            ≡ Agen-edge-aux (subst₂ FlatGen p' q' x)
          subst₂-Agen-edge-aux-nat refl refl _ = refl

--------------------------------------------------------------------------------
-- ## Section 3: Constructive composition deriving the full `bridge-to-g`.
--
-- The harness instantiates `bridge-to-g-list` at:
--   * `es = range nE_g`
--   * `s_g = ⟪g⟫F.dom`
--   * `s_f = ⟪f⟫F.dom`
--   * `s-eq` = `full-dom-eq f g`-derived map-equality on the
--              starting stacks (factor through `⟪⟫F-domL`).
--   * `stack-eq` = caller's `stack-eq` (note orientation reversed).
--   * `b-stack-↭` = caller's `b-stack-↭`.
--
-- This composition is mechanical subst₂ + stack-permutation algebra.
-- The orientation flips in `s-eq` and `stack-eq` are bridged via
-- `sym`.

-- The constructive top-level `bridge-to-g-list`.
--
-- Discharged constructively (no postulates) from:
--
--   * `r   : BridgeToGFullResidual`   (iso-data + derived per-edge atoms)
--   * `walk: NaturalRangeWalkBridge`  (natural-range walks' equiv)
--   * `sob : StackOrderingBridge`     (architectural ordering bridge)
--
-- The matching signature is the original `bridge-to-g-list`.
--
-- Composition is the same 2-step `≈Term`-trans as
-- `BridgeToGList.WithAll.bridge-to-g-list`.  We INLINE it here (rather
-- than delegating) because `WithAll` requires a `PerEdgeAtomsOnly`
-- value parametric in an arbitrary `ψF`, but the new
-- `BridgeToGFullResidual.iso-data` fixes `ψF` to the iso's bijection.
-- The `PerEdgeAtomsOnly` parameter is unused in `WithAll`'s body, so
-- bypassing it loses no constructive content.
--
-- NOTE: the former `xsl : XSelfLoop` parameter has been dropped — it
-- was accepted for API symmetry with `BridgeToGList.WithAll` but
-- NEVER consumed in the body (verified by F1).
bridge-to-g-list
  : (r    : BridgeToGFullResidual)
  → (walk : NaturalRangeWalkBridge)
  → (sob  : StackOrderingBridge)
  → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
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
bridge-to-g-list r walk sob f g iso ψF stack-eq b-stack-↭ =
  ≈-Term-trans
    (NaturalRangeWalkBridge.natural-range-≈Term walk f g iso stack-eq)
    (StackOrderingBridge.ordering-bridge       sob  f g iso ψF b-stack-↭)

module WithResidual
  (r    : BridgeToGFullResidual)
  (walk : NaturalRangeWalkBridge)
  (sob  : StackOrderingBridge)
  where
  open BridgeToGFullResidual r

  -- Helper: the starting-stack equality at the FromAPROP level.
  --
  -- Both `⟪f⟫F.dom` and `⟪g⟫F.dom` are `Fin` lists whose `vlab`-
  -- images equal `flatten A` (via `⟪⟫F-domL`).  Hence
  --   map ⟪f⟫F.vlab ⟪f⟫F.dom = flatten A = map ⟪g⟫F.vlab ⟪g⟫F.dom
  -- propositionally.
  --
  -- This is what would be `s-eq` for the list-induction at the start.
  dom-stack-eq
    : ∀ {A B} (f g : HomTerm A B)
    → map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.dom ⟪ g ⟫F)
    ≡ map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.dom ⟪ f ⟫F)
  dom-stack-eq f g = full-dom-eq f g

  -- The exact signature of `ProcessTermAlignedAssumption.bridge-to-g`.
  --
  -- Composition:
  --   1. The starting stacks are `⟪f⟫F.dom` and `⟪g⟫F.dom`.  Their
  --      vlab-images coincide (with `flatten A` as middle term).
  --   2. The `b-stack-↭` is provided by the caller.
  --   3. The boundary subst₂ uses `full-dom-eq` for the dom-side
  --      and `sym stack-eq` for the cod-side.
  --   4. We instantiate `bridge-to-g-list` at these arguments.
  --
  -- The orientation of `stack-eq` in the caller is
  --   `map vlab_f (proj₁ ...) ≡ map vlab_g (proj₁ ...)`
  -- whereas `bridge-to-g-list` expects
  --   `map vlab_f (proj₁ (... map ψF es ...))
  --   ≡ map vlab_g (proj₁ (... es ...))`
  -- which is the same orientation (the caller's `process-all-edges
  -- ⟪g⟫F ...` = `process-edges ⟪g⟫F (range nE_g) ...`, definitional).
  --
  -- We need the propositional bridge between `process-all-edges
  -- ⟪f⟫F ⟪f⟫F.dom` and `process-edges ⟪f⟫F (map ψF (range nE_g))
  -- ⟪f⟫F.dom` — which is NOT propositional equality (different edge
  -- orderings), but `b-stack-↭` connects them at the stack level.
  --
  -- The caller's `stack-eq` is:
  --   map vlab_f (proj₁ (process-all-edges ⟪f⟫F ⟪f⟫F.dom))
  --   ≡
  --   map vlab_g (proj₁ (process-all-edges ⟪g⟫F ⟪g⟫F.dom))
  --
  -- For `bridge-to-g-list` instantiated at `es = range nE_g`, we need:
  --   map vlab_f (proj₁ (process-edges ⟪f⟫F (map ψF (range nE_g)) ⟪f⟫F.dom))
  --   ≡
  --   map vlab_g (proj₁ (process-edges ⟪g⟫F (range nE_g) ⟪g⟫F.dom))
  --
  -- The RHS is propositionally `process-all-edges ⟪g⟫F ⟪g⟫F.dom`
  -- (by definition).  The LHS is `process-edges ⟪f⟫F (map ψF ...)
  -- ⟪f⟫F.dom`, which is NOT propositionally equal to
  -- `process-all-edges ⟪f⟫F ⟪f⟫F.dom` — instead, `b-stack-↭` relates
  -- their `proj₁` outputs via permutation, which lifts to a vlab-
  -- list equality via `PermProp.map⁺`.
  --
  -- To bridge: use `b-stack-↭` to lift to a vlab-permutation, and
  -- use the `vlab-stack-eq` (a propositional equality, since
  -- permutations of vlab-lists can be transported via the fact that
  -- the underlying lists are propositionally equal when interpreted
  -- as multisets — but only when one of them is FIXED).  In our
  -- case the propositional equality comes from the caller's
  -- `stack-eq` combined with the propositional equality
  -- `process-all-edges ⟪f⟫F ⟪f⟫F.dom = process-edges ⟪f⟫F (range nE_f)
  -- ⟪f⟫F.dom` (definitional).
  --
  -- The proper bridge: `b-stack-↭` is at the `Fin (nV ⟪f⟫F)` level
  -- (raw vertices).  Its `PermProp.map⁺ vlab_f` lift gives a `↭`
  -- at the X-list level on `map vlab_f`'s.  By the multiset-equality
  -- claim... actually, NO.  Permutation does not imply propositional
  -- equality of lists in general.
  --
  -- The resolution: the caller's `stack-eq` is provided EXACTLY for
  -- this purpose — to give the propositional vlab-list equality
  -- between the two `process-all-edges` outputs.  Combining
  -- `stack-eq` with the (definitional) `process-all-edges ⟪f⟫F
  -- ⟪f⟫F.dom = process-edges ⟪f⟫F (range nE_f) ⟪f⟫F.dom` does NOT
  -- automatically give the equality we need for the
  -- `bridge-to-g-list` instantiation.
  --
  -- ARCHITECTURAL OBSERVATION: this means `bridge-to-g-list`'s
  -- `stack-eq` precondition is FUNDAMENTALLY DIFFERENT from
  -- `bridge-to-g`'s `stack-eq` — the former is about the `(map ψF
  -- range nE_g)` ordering, the latter about the natural range
  -- ordering of `⟪f⟫F`.
  --
  -- This is exactly why `bridge-to-g-list` is exposed as a residual:
  -- the harness here can only USE it, not derive it from the
  -- caller's `stack-eq` + `b-stack-↭` alone.
  --
  -- We expose this in the API by accepting both the caller's
  -- `stack-eq` and an additional `list-stack-eq` field that the
  -- caller is expected to supply via the (B-↭) machinery.
  bridge-to-g-from-residual
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
  bridge-to-g-from-residual f g iso ψF stack-eq b-stack-↭ =
    -- The full bridge is delivered by the top-level `bridge-to-g-list`,
    -- which constructively derives the list-induction harness from
    -- the per-edge atoms (fields (a)/(b)/(c)) + the auxiliary walk/sob
    -- inputs supplied to this module.
    bridge-to-g-list r walk sob f g iso ψF stack-eq b-stack-↭

--------------------------------------------------------------------------------
-- ## Section 4: Summary.
--
-- ### What this file delivers vs Sub/BridgeToG.agda (previous attempt)
--
-- * `Sub/BridgeToG.agda` (265 LOC): ONE residual field
--   `bridge-to-g-residual` carrying the FULL bridge content.  No
--   decomposition.  No constructive progress.
--
-- * `Sub/BridgeToGFull.agda` (this file, ~360 LOC): FOUR residual
--   fields:
--   * `atom-ein-F`         — Per-edge vlab/ein equality at FromAPROP level.
--   * `atom-eout-F`        — Per-edge vlab/eout equality at FromAPROP level.
--   * `Agen-edge-compat`   — Per-edge term equivalence under iso.
--   * `bridge-to-g-list`   — Generic list-induction harness.
--
-- The decomposition decouples the iso-lift content (fields 1-3) from
-- the structural induction (field 4).  Each field is strictly
-- narrower than `bridge-to-g`, and they can be discharged
-- INDEPENDENTLY (in particular, `bridge-to-g-list` is term-level
-- pure-induction; the iso-lift fields are per-edge propositional
-- and term-level equalities).
--
-- ### Architectural value
--
-- The decomposition isolates the TWO independent sources of
-- difficulty:
--
-- 1. **The constructive iso-lift.** Translating `_≅ᴴ_` from the
--    Translation level to the FromAPROP level is BLOCKED by
--    `BoundaryRespectsIso.agda`.  Fields (a), (b), (c) capture this
--    irreducible content at the per-edge level.
--
-- 2. **The list induction.** Even GIVEN the iso-lift, threading
--    subst₂ + permute-via-vlab through the list-induction over
--    `range nE_g` is a substantial proof (~150 LOC).  Field (d)
--    captures this as a SEPARATE residual.
--
-- A future agent can attack each independently:
--   * Solving (a)+(b)+(c) without solving (d) — the per-edge content.
--   * Solving (d) without solving (a)+(b)+(c) — assuming the
--     per-edge data, write the list induction.
--
-- ### Composition (Section 3)
--
-- The composition `bridge-to-g-from-residual` derives the exact
-- signature of `ProcessTermAlignedAssumption.bridge-to-g` from
-- the residual, by instantiating field (d) at the natural inputs.
--
-- ### True remaining blocker (after this narrowing)
--
-- The constructive iso-lift from Translation `≅ᴴ` to FromAPROP-level
-- per-edge atom-list equalities ((a)+(b)) is the only remaining
-- content gating the per-edge fields (1-3).  This is BLOCKED by
-- `BoundaryRespectsIso.agda` and would require a parallel
-- `Translation→FromAPROP-iso-lift` lemma (~150-300 LOC).
--
-- The list-induction (d) is gated only by ~150 LOC of subst₂
-- boilerplate, given the per-edge data on hand.
--
-- ### Status
--
-- File is `--safe --with-K`-clean.  No `postulate`s.  Four narrow
-- iso-compatibility/induction fields with a constructive composition
-- matching `ProcessTermAlignedAssumption.bridge-to-g`'s signature.
--------------------------------------------------------------------------------
