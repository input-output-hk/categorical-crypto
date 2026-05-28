{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of `BridgeToGFullResidual.bridge-to-g-list`
-- from `Sub/BridgeToGFull.agda`, ASSUMING:
--
--   * The 3 per-edge atoms from `BridgeToGFullResidual`:
--       - `atom-ein-F`        (per-edge vlab/ein equality at FromAPROP level)
--       - `atom-eout-F`       (per-edge vlab/eout equality at FromAPROP level)
--       - `Agen-edge-compat`  (per-edge term equivalence under iso)
--   * The X-self-loop postulate `XSelfLoop.X-permute-self-loop-id`
--     (which yields full `permute-≈Term-coherence` via
--     `PermuteCoherenceShared.FromXSelfLoop`).
--
-- ## File overview
--
-- This file narrows `bridge-to-g-list` (a sub-field of
-- `BridgeToGFullResidual`) into THREE independent residual pieces:
--
--   (P-edge)     `PerEdgeAtomsOnly`           — the 3 per-edge atoms.
--   (P-walk)     `NaturalRangeWalkBridge`     — the natural-range
--                                                walks' `≈Term`-
--                                                equivalence
--                                                (`process-term-
--                                                 aligned` shape).
--   (P-ordering) `StackOrderingBridge`        — the architectural
--                                                ordering bridge from
--                                                ⟪f⟫F's natural-range
--                                                walk to its ψF-
--                                                image-range walk.
--
-- The composition `bridge-to-g-list` (under
-- `WithAtomsAndXSL` ∘ `WithStackOrdering`) is then a simple
-- `≈Term`-transitivity through (P-walk) + (P-ordering).
--
-- ## Honest assessment of constructive content
--
-- Even with the 3 per-edge atoms + XSL on hand, the FULL discharge
-- of `bridge-to-g-list` requires TWO additional bits of content:
--
--   (a) the list-induction over `range nE_g` (the "(P-walk)"
--       residual) — purely subst₂ algebra given the atoms +
--       `permute-≈Term-coherence`;
--   (b) the architectural ordering bridge from natural-range to
--       ψF-image-range — the (B-↭)/(swap-atom-aligned) content,
--       FUNDAMENTALLY different from the per-edge iso compatibility.
--
-- (a) is mechanical given the atoms + XSL, but its FULL inline
-- proof is ~100-150 LOC of `≈Term`-chain reasoning over the recursive
-- `process-edges` definition; we expose it as a single narrow
-- residual `NaturalRangeWalkBridge`.
--
-- (b) is GENUINELY a separate piece of mathematical content (the
-- list-permutation content from `swap-atom-aligned`, isomorphic to
-- `process-edges-↭-topo`); we expose it as `StackOrderingBridge`.
--
-- ## File structure
--
--   Section 1: Common imports + `subst₂`-algebra helpers.
--   Section 2: The atoms-only record (`PerEdgeAtomsOnly`).
--   Section 3: The natural-range walk bridge (`NaturalRangeWalkBridge`).
--   Section 4: The architectural ordering bridge (`StackOrderingBridge`).
--   Section 5: Composition — `WithAll` derives `bridge-to-g-list` from
--              (P-edge) + (P-walk) + (P-ordering) + XSL.
--   Section 6: Summary.
--
-- ## Status
--
--   * --safe --with-K-clean.  No `postulate` declarations.
--   * 3 narrow residual records, each carrying ONE piece of content.
--   * Composition `WithAll.bridge-to-g-list` matches the parent
--     signature verbatim.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToGList
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
         Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTerm sig-dec
  using (full-dom-eq; full-cod-eq)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using (≡⇒≈Term; subst₂-resp-≈Term)
open import Categories.APROP.Hypergraph.Completeness.Discharge.PermuteCoherenceShared
  sig-dec
  using (XSelfLoop; PermuteCoherence; module FromXSelfLoop)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## Section 1: Common helpers.
--
-- Local `subst₂`-algebra helpers, mirroring those in `BridgeToGFull`
-- (re-stated here so this file is self-contained).

private
  -- `subst₂ HomTerm refl refl x ≡ x`.
  subst₂-refl-HomTerm
    : ∀ {A B} (x : HomTerm A B)
    → subst₂ HomTerm refl refl x ≡ x
  subst₂-refl-HomTerm _ = refl

  -- Composition of nested `subst₂` transports.
  subst₂-trans-HomTerm
    : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
        (p₁ : A₁ ≡ A₂) (p₂ : A₂ ≡ A₃)
        (q₁ : B₁ ≡ B₂) (q₂ : B₂ ≡ B₃)
        (x : HomTerm A₁ B₁)
    → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ x)
    ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) x
  subst₂-trans-HomTerm refl refl refl refl _ = refl

  -- `subst₂` along `sym` undoes the original.
  subst₂-sym-HomTerm
    : ∀ {A₁ A₂ B₁ B₂} (p : A₁ ≡ A₂) (q : B₁ ≡ B₂) (x : HomTerm A₁ B₁)
    → subst₂ HomTerm (sym p) (sym q) (subst₂ HomTerm p q x) ≡ x
  subst₂-sym-HomTerm refl refl _ = refl

--------------------------------------------------------------------------------
-- ## Section 2: Per-edge atoms (atoms-only, no list-induction).
--
-- A LOCAL record of just the 3 per-edge fields that
-- `BridgeToGFullResidual` carries.  Re-exposed here (rather than open-
-- imported from `BridgeToGFullResidual`) so the consumer can supply
-- the atoms WITHOUT being forced to also supply the residual
-- `bridge-to-g-list` field (the very field we're discharging here).

record PerEdgeAtomsOnly : Set where
  field
    -- (a) Per-edge `vlab ∘ ein` equality at the FromAPROP level.
    atom-ein-F
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.ein  ⟪ f ⟫F (ψF e))
      ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.ein  ⟪ g ⟫F e)

    -- (b) Per-edge `vlab ∘ eout` equality at the FromAPROP level.
    atom-eout-F
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.eout ⟪ f ⟫F (ψF e))
      ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.eout ⟪ g ⟫F e)

    -- (c) Per-edge `Agen-edge` term equivalence under iso.
    Agen-edge-compat
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → subst₂ HomTerm
          (cong unflatten (atom-ein-F  f g iso ψF e))
          (cong unflatten (atom-eout-F f g iso ψF e))
          (Agen-edge ⟪ f ⟫F (ψF e))
        ≈Term Agen-edge ⟪ g ⟫F e

--------------------------------------------------------------------------------
-- ## Section 3: The natural-range walk bridge.
--
-- The (P-walk) residual: an `≈Term`-equivalence of the two
-- `process-all-edges` outputs (modulo boundary subst₂), under the
-- iso compatibility.
--
-- This is the CONTENT of the list-induction over `range nE_g`:
-- given the per-edge atoms + `permute-≈Term-coherence`, threading
-- subst₂ through `edge-step`/`process-edges` aligns the two natural-
-- range walks.  No ψF, no `b-stack-↭`, no permute-via-vlab
-- composition — just the bare alignment shape.
--
-- Strictly narrower than the parent `bridge-to-g-list`:
--   * Conclusion shape matches `process-term-aligned` exactly.
--   * No ψF (just the iso-induced edge correspondence).
--   * No b-stack-↭ (just the boundary subst₂).
--
-- Status of constructive discharge: a future agent inlines the
-- list-induction here, using `PerEdgeAtomsOnly` + `XSelfLoop`-
-- derived `permute-≈Term-coherence`.  Estimated ~100-150 LOC of
-- `≈Term`-chain + `subst₂`-shuffle inside `process-edges` recursion.
--
-- NOTE: this record IS the natural-range version of the existing
-- `ProcessTermAssumption.process-term-aligned` from
-- `Discharge/ProcessTerm.agda`.  We re-state it here (rather than
-- import) so this file's residuals are self-contained.

record NaturalRangeWalkBridge : Set where
  field
    natural-range-≈Term
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

--------------------------------------------------------------------------------
-- ## Section 4: The architectural ordering bridge.
--
-- The (P-ordering) residual: the TERM-level bridge from ⟪f⟫F's
-- "natural-Fin-order" walk to its "ψF-image-order" walk.
--
-- Why this is FUNDAMENTALLY a separate residual:
--
-- `process-all-edges ⟪f⟫F dom_f`  ≠ ... ≠
-- `process-edges ⟪f⟫F (map ψF (range nE_g)) dom_f`
--
-- — these two walks traverse ⟪f⟫F's edges in DIFFERENT orders.  The
-- `b-stack-↭` is a vertex-level permutation relating their `proj₁`
-- outputs, but the `proj₂` outputs are NOT propositionally equal.
-- They are `≈Term`-equivalent modulo the permute-via-vlab factor —
-- the content of `process-edges-↭-topo` + `swap-atom-aligned` from
-- `ProcessTermAlignedAssumption`.
--
-- This residual EXPOSES that bridge as a SINGLE field.

record StackOrderingBridge : Set where
  field
    -- Term-level bridge between ⟪f⟫F's natural-range walk and its
    -- ψF-image-range walk, modulo the stack `b-stack-↭`.
    ordering-bridge
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (b-stack-↭ :
            proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭
            proj₁ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)))
      → proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
        ≈Term
        permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 5: Composition.
--
-- Given:
--   * `atoms : PerEdgeAtomsOnly`         (the 3 per-edge atoms)
--   * `xsl   : XSelfLoop`                (the X-level self-loop postulate)
--   * `walk  : NaturalRangeWalkBridge`   (natural-range walks' equiv)
--   * `sob   : StackOrderingBridge`      (architectural ordering bridge)
--
-- We derive `bridge-to-g-list` matching the signature in
-- `BridgeToGFullResidual`.
--
-- ## Composition steps
--
-- The `bridge-to-g-list` statement is:
--
--   subst₂ HomTerm (cong unflatten (full-dom-eq f g))
--                   (cong unflatten (sym stack-eq))
--                   (proj₂ (process-all-edges ⟪g⟫F dom_g))
--   ≈Term
--   permute-via-vlab _ (sym b-stack-↭)
--     ∘ proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g)) dom_f)
--
-- We chain:
--
--   LHS
--   ≈Term [walk.natural-range-≈Term f g iso stack-eq]
--     proj₂ (process-all-edges ⟪f⟫F dom_f)
--   ≈Term [sob.ordering-bridge f g iso ψF b-stack-↭]
--     permute-via-vlab _ (sym b-stack-↭)
--     ∘ proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g)) dom_f)
--   = RHS.
--
-- The composition is a 2-step `≈Term-trans`.

module WithAll
  (atoms : PerEdgeAtomsOnly)
  (xsl   : XSelfLoop)
  (walk  : NaturalRangeWalkBridge)
  (sob   : StackOrderingBridge)
  where

  open PerEdgeAtomsOnly atoms
  open NaturalRangeWalkBridge walk
  open StackOrderingBridge sob

  -- Derive `PermuteCoherence` from XSL.  Currently unused in the
  -- composition itself (because the `natural-range-≈Term` already
  -- bakes in the result of `permute-≈Term-coherence`), but exposed
  -- here so future inlinings of the list-induction can consume it
  -- directly.
  private
    permCoh : PermuteCoherence
    permCoh = FromXSelfLoop.permuteCoherence xsl

  open PermuteCoherence permCoh

  ------------------------------------------------------------------
  -- The discharge of `bridge-to-g-list`.
  --
  -- Composition: chain (P-walk) then (P-ordering).

  bridge-to-g-list
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
  bridge-to-g-list f g iso ψF stack-eq b-stack-↭ =
    ≈-Term-trans
      (natural-range-≈Term f g iso stack-eq)
      (ordering-bridge f g iso ψF b-stack-↭)

--------------------------------------------------------------------------------
-- ## Section 6: Summary.
--
-- ### What this file delivers
--
-- This file decomposes `BridgeToGFullResidual.bridge-to-g-list` into
-- THREE INDEPENDENT residual pieces:
--
--   (P-edge)     `PerEdgeAtomsOnly`         (the 3 per-edge atoms).
--   (P-walk)     `NaturalRangeWalkBridge`   (`process-term-aligned`-
--                                            shape: the natural-range
--                                            walks' `≈Term`-
--                                            equivalence).
--   (P-ordering) `StackOrderingBridge`      (the (B-↭) architectural
--                                            ordering bridge).
--
-- Each residual carries STRICTLY DIFFERENT content:
--
--   * (P-edge)  : per-edge propositional/term-level iso compatibility.
--   * (P-walk)  : the list-induction over `range nE_g` (no iso
--                  compatibility beyond the per-edge atoms, but
--                  requires `permute-≈Term-coherence` derivable
--                  from XSL).
--   * (P-ordering): the structural list-permutation content from
--                    `swap-atom-aligned` (no iso compatibility, no
--                    per-edge content).
--
-- The composition `WithAll.bridge-to-g-list` is a TWO-STEP `≈Term`-
-- transitivity through (P-walk) + (P-ordering).
--
-- ### Architectural value
--
-- After this decomposition, a downstream agent has THREE
-- independent attack surfaces:
--
--   * Discharge (P-edge) from the iso's `ψ-ein` / `ψ-eout` / `ψ-elab`
--     fields (blocked by `BoundaryRespectsIso.agda` — the Translation
--     iso doesn't lift cleanly to FromAPROP).
--   * Discharge (P-walk) constructively from (P-edge) + XSL
--     (estimated ~100-150 LOC of `subst₂`-shuffling).
--   * Discharge (P-ordering) from the (B-↭) / `swap-atom-aligned`
--     machinery (independent of the iso compatibility).
--
-- The composition `WithAll.bridge-to-g-list` is ~5 LOC of
-- `≈Term`-trans.  The constructive content has been COMPLETELY
-- offloaded to the three residual records.
--
-- ### Trust delta
--
-- Compared to the parent `BridgeToGFullResidual.bridge-to-g-list`:
--
--   * `bridge-to-g-list` is ONE quantifier-rich statement universally
--     quantified over `(f, g, iso, ψF, stack-eq, b-stack-↭)`.
--
--   * Our decomposition:
--     - (P-edge):    3 per-edge propositional/`≈Term` statements
--                     (no list induction, no architectural mismatch).
--     - (P-walk):    1 `≈Term`-equivalence on natural-range walks
--                     (the LIST INDUCTION isolated; no architectural
--                     mismatch).
--     - (P-ordering): 1 `≈Term`-bridge on architectural mismatch
--                     (no list induction, no iso compatibility).
--
-- Each piece is STRICTLY narrower than the parent.
--
-- ### Status
--
-- File is `--safe --with-K`-clean.  No `postulate` declarations.
-- The composition `WithAll.bridge-to-g-list` provides the FULL
-- `BridgeToGFullResidual.bridge-to-g-list` signature given the
-- three residuals.
--------------------------------------------------------------------------------
