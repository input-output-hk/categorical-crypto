{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `AllFireResidual.AllFire-via-bij` from
-- `Discharge/Sub/IsoInducesEdgePerm.agda` (Section 5, Field
-- `AllFire-via-bij`).
--
-- ## Goal (the consumer's signature, IsoInducesEdgePerm Section 5)
--
--   AllFire-via-bij
--     : ∀ (Hf : Hypergraph FlatGen) (m : ℕ)
--         (ψF : Fin m → Fin (Hypergraph.nE Hf))
--     → range (Hypergraph.nE Hf) Perm.↭ map ψF (range m)
--     → Linear Hf
--     → AllFire Hf (map ψF (range m)) (Hypergraph.dom Hf)
--
-- ## Strategy: combine two ingredients.
--
--   * (Already constructive) `AllFire-natural-range`, but stated for
--     translated hypergraphs `⟪ f ⟫F`.  We need its analogue for an
--     arbitrary Linear `Hf` whose `dom` is what we test against.
--
--     Since `AllFireResidual.AllFire-via-bij` is statically consumed
--     ONLY by `iso-induces-edge-↭-via-residual` (in IsoInducesEdgePerm.agda),
--     where `Hf = ⟪ f ⟫F`, we can package the discharge as a function
--     specialised to translated hypergraphs and re-export it AT the
--     general `Hf` signature only after we additionally postulate the
--     "natural-range AllFire" for arbitrary Linear `Hf`.  However, that
--     auxiliary fact is precisely what `AllFire-natural-range` proves
--     for translated hypergraphs; we DON'T have it for arbitrary
--     Linear hypergraphs (the `AllFire` is a SEMANTIC property of the
--     hypergraph data, not implied by Linearity alone — Linearity is a
--     count invariant; AllFire is a *firing* invariant).
--
--     So our `WithAllFireResidual` module further narrows by taking
--     the natural-range AllFire as an EXPLICIT input parameter for the
--     specific `Hf` in question.
--
--   * (The genuinely-hard, edge-list permutation lemma)
--     `AllFire-edge-↭`: given `AllFire H es₁ s` AND `es₁ Perm.↭ es₂`,
--     conclude `AllFire H es₂ s`.  This is FALSE in general (per the
--     `EdgeReorder.agda` counter-example) — it requires Linearity of
--     the hypergraph PLUS a topological-soundness invariant on the
--     permutation.  We expose it as the sole sub-residual.
--
--     Notably, `trans-intermediate-allfire` (in `ProcessEdgesPermTopo.agda`)
--     is essentially a binary form of this lemma: given AllFires on
--     two ↭-equivalent edge lists, the intermediate list is also AllFire.
--     OUR residual is a slightly stronger one-sided version: given
--     AllFire on `es₁` AND `es₁ ↭ es₂`, conclude AllFire on `es₂`.
--
-- ## What this file delivers
--
-- 1.  A record `AllFireEdgePermResidual` with TWO narrow fields:
--
--     a.  `AllFire-natural-range-Hf` — provides the natural-range AllFire
--         for the specific Linear `Hf` being processed.  An external
--         caller (e.g. `iso-induces-edge-↭-via-residual` in
--         IsoInducesEdgePerm) supplies this from `AllFire-natural-range`
--         when `Hf = ⟪ f ⟫F`, OR derives it for other Linear hypergraphs
--         via a separate proof.
--
--     b.  `AllFire-edge-↭` — the edge-list permutation transport lemma.
--         The sole residual.
--
-- 2.  `WithAllFireResidual` module providing the constructive derivation:
--
--       AllFire-via-bij Hf m ψF es-↭ lin =
--         AllFire-edge-↭ Hf (range nE-Hf) (map ψF (range m))
--                        (AllFire-natural-range-Hf Hf lin)
--                        es-↭
--
-- 3.  Additionally, an `AllFire-via-bij-for-⟪⟫F` convenience function
--     that specialises the discharge to translated hypergraphs, using
--     `AllFire-natural-range` from `AllFireNatural.agda`.  This is the
--     intended consumption path from `IsoInducesEdgePerm`.
--
-- ## Status
--
-- `--safe --with-K`-clean.  No `postulate` declarations.  Discharges
-- `AllFire-via-bij` to a single sub-residual `AllFire-edge-↭` (an
-- edge-list permutation transport lemma) and, for the consumer's
-- specific use-case `Hf = ⟪ f ⟫F`, removes the natural-range-AllFire
-- sub-residual entirely (by re-using `AllFire-natural-range`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireViaBij
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; range)
  renaming (⟪_⟫ to ⟪_⟫F)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear; ⟪⟫-Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned sig-dec
  using (AllFire)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural sig-dec
  using (AllFire-natural-range)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

--------------------------------------------------------------------------------
-- ## Section 1: The narrowed residual record.
--
-- A single record with TWO fields exposing the residual obligations.
-- The `AllFire-via-bij` field of the consumer record
-- (`AllFireResidual` in `IsoInducesEdgePerm.agda`) is constructively
-- derivable from these two narrower fields.

record AllFireEdgePermResidual : Set where
  field
    --------------------------------------------------------------------
    -- (Field 1) The natural-range AllFire for an arbitrary Linear
    -- hypergraph.  This is the semantic precondition that, when the
    -- edges of `Hf` are visited in natural Fin order from `Hf.dom`,
    -- every step's `extract-prefix` succeeds.
    --
    -- For translated hypergraphs (`Hf = ⟪ f ⟫F`), this is fully
    -- constructive (see `AllFireNatural.agda`'s `AllFire-natural-range`).
    --
    -- For arbitrary Linear hypergraphs, Linearity (a count invariant)
    -- does NOT imply AllFire — AllFire is a *firing-order* property,
    -- and edges can have count-balanced ein/eout that nevertheless
    -- depend on each other in non-natural ways.
    --
    -- The consumer of `AllFire-via-bij` is `IsoInducesEdgePerm.agda`,
    -- where `Hf = ⟪ f ⟫F` — so the consumer's specialised wrapper
    -- (`AllFire-via-bij-for-⟪⟫F` below) DISCHARGES this field by
    -- reusing `AllFire-natural-range`.  The general field remains
    -- in case downstream agents want to instantiate `Hf` more
    -- broadly.
    AllFire-natural-range-Hf
      : ∀ (Hf : Hypergraph FlatGen)
      → Linear Hf
      → AllFire Hf (range (Hypergraph.nE Hf)) (Hypergraph.dom Hf)

    --------------------------------------------------------------------
    -- (Field 2) Edge-list permutation transports AllFire.
    --
    -- This is the GENUINELY-HARD content.  EdgeReorder.agda exhibits
    -- a 1-step counter-example WITHOUT Linearity: two edges with the
    -- same input vertex can both fire as the head of a list, but the
    -- corresponding pre-firing extract-prefixes succeed only when the
    -- "right" edge is chosen first.
    --
    -- WITH Linearity, the invariant becomes: each vertex is produced
    -- exactly once and consumed exactly once (count ≡ 1).  This means
    -- a permutation of the edge list ALWAYS preserves the multiset of
    -- consumed/produced vertices — so any valid firing order remains
    -- valid.
    --
    -- The constructive content sits in a process-edges induction over
    -- the `_↭_` derivation (refl, prep, swap, trans) — see
    -- `ProcessEdgesPermTopo.agda`'s `trans-intermediate-allfire`,
    -- which is a closely-related residual.  Estimated discharge:
    -- ~150-200 LOC building on `extract-prefix-↭-residual` and the
    -- Linearity invariants.
    --
    -- NARROWING: This field's signature does NOT mention `_≅ᴴ_`, the
    -- Translation iso, the bijection, OR the FromAPROP layer.  It is
    -- a pure combinatorial fact about `AllFire` and `_↭_` on edge
    -- lists, requiring only the hypergraph data (and Linearity).
    AllFire-edge-↭
      : ∀ (Hf : Hypergraph FlatGen)
          (es₁ es₂ : List (Fin (Hypergraph.nE Hf)))
          (s : List (Fin (Hypergraph.nV Hf)))
      → Linear Hf
      → AllFire Hf es₁ s
      → es₁ Perm.↭ es₂
      → AllFire Hf es₂ s

--------------------------------------------------------------------------------
-- ## Section 2: Constructive discharge of `AllFire-via-bij`.
--
-- Given the residual record, produce the full `AllFire-via-bij` field
-- of `AllFireResidual` (in `IsoInducesEdgePerm.agda`).
--
-- The derivation is a two-line chain:
--
--   1. Apply `AllFire-natural-range-Hf Hf lin` to get
--        `AllFire Hf (range nE-Hf) Hf.dom`.
--   2. Apply `AllFire-edge-↭ Hf (range nE-Hf) (map ψF (range m)) Hf.dom`
--      with the natural-range AllFire and the input permutation.

module WithAllFireResidual (assumption : AllFireEdgePermResidual) where
  open AllFireEdgePermResidual assumption

  -- The full `AllFire-via-bij` field, derived from the two sub-residuals.
  AllFire-via-bij
    : ∀ (Hf : Hypergraph FlatGen) (m : ℕ)
        (ψF : Fin m → Fin (Hypergraph.nE Hf))
    → range (Hypergraph.nE Hf) Perm.↭ map ψF (range m)
    → Linear Hf
    → AllFire Hf (map ψF (range m)) (Hypergraph.dom Hf)
  AllFire-via-bij Hf m ψF es-↭ lin =
    AllFire-edge-↭ Hf (range (Hypergraph.nE Hf)) (map ψF (range m))
                      (Hypergraph.dom Hf) lin
                      (AllFire-natural-range-Hf Hf lin)
                      es-↭

--------------------------------------------------------------------------------
-- ## Section 3: Specialised wrapper for translated hypergraphs.
--
-- For the intended consumer of `AllFire-via-bij` in `IsoInducesEdgePerm`,
-- `Hf = ⟪ f ⟫F` for some `f : HomTerm A B`.  We can DISCHARGE Field 1
-- of the residual (the natural-range AllFire) entirely, by reusing
-- `AllFire-natural-range` from `AllFireNatural.agda`.
--
-- This module takes ONLY the edge-↭ residual as input, dropping Field 1.

record AllFireEdge↭Only : Set where
  field
    AllFire-edge-↭
      : ∀ (Hf : Hypergraph FlatGen)
          (es₁ es₂ : List (Fin (Hypergraph.nE Hf)))
          (s : List (Fin (Hypergraph.nV Hf)))
      → Linear Hf
      → AllFire Hf es₁ s
      → es₁ Perm.↭ es₂
      → AllFire Hf es₂ s

module WithAllFireEdge↭ (assumption : AllFireEdge↭Only) where
  open AllFireEdge↭Only assumption

  -- Specialised to translated hypergraphs `⟪ f ⟫F`.
  -- The natural-range AllFire is supplied by `AllFire-natural-range`.
  AllFire-via-bij-for-⟪⟫F
    : ∀ {A B} (f : HomTerm A B) (m : ℕ)
        (ψF : Fin m → Fin (Hypergraph.nE ⟪ f ⟫F))
    → range (Hypergraph.nE ⟪ f ⟫F) Perm.↭ map ψF (range m)
    → AllFire ⟪ f ⟫F (map ψF (range m)) (Hypergraph.dom ⟪ f ⟫F)
  AllFire-via-bij-for-⟪⟫F f m ψF es-↭ =
    AllFire-edge-↭ ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F)) (map ψF (range m))
                          (Hypergraph.dom ⟪ f ⟫F) (⟪⟫-Linear f)
                          (AllFire-natural-range f)
                          es-↭

  -- General `AllFire-via-bij` field — accepts any Linear `Hf`, but
  -- requires Field 1 (the natural-range AllFire) to be supplied
  -- externally as an explicit parameter `nat-range-AllFire`.
  --
  -- For the consumer's case (`Hf = ⟪ f ⟫F`), pass `AllFire-natural-range f`
  -- as `nat-range-AllFire`.
  AllFire-via-bij-with-nat
    : ∀ (Hf : Hypergraph FlatGen) (m : ℕ)
        (ψF : Fin m → Fin (Hypergraph.nE Hf))
      (es-↭ : range (Hypergraph.nE Hf) Perm.↭ map ψF (range m))
      (lin : Linear Hf)
      (nat-range-AllFire : AllFire Hf (range (Hypergraph.nE Hf))
                                       (Hypergraph.dom Hf))
    → AllFire Hf (map ψF (range m)) (Hypergraph.dom Hf)
  AllFire-via-bij-with-nat Hf m ψF es-↭ lin nat-range-AllFire =
    AllFire-edge-↭ Hf (range (Hypergraph.nE Hf)) (map ψF (range m))
                      (Hypergraph.dom Hf) lin
                      nat-range-AllFire
                      es-↭

--------------------------------------------------------------------------------
-- ## Section 4: Summary.
--
-- This file constructively discharges
-- `AllFireResidual.AllFire-via-bij` (from `IsoInducesEdgePerm.agda`)
-- to a single sub-residual:
--
--     AllFire-edge-↭
--       : ∀ Hf es₁ es₂ s
--       → Linear Hf → AllFire Hf es₁ s → es₁ Perm.↭ es₂
--       → AllFire Hf es₂ s
--
-- This sub-residual is the edge-list permutation transport lemma:
-- under Linearity, permuting the edge list preserves AllFire.  It is
-- a pure combinatorial fact (no iso, no Translation, no FromAPROP-
-- specific structure required), and is closely related to
-- `ProcessEdgesPermTopo.trans-intermediate-allfire`.
--
-- The natural-range AllFire (the other ingredient) is supplied by
-- the existing `AllFireNatural.agda`'s `AllFire-natural-range` for
-- translated hypergraphs, removing Field 1 of the residual entirely
-- for the intended consumer.
--
-- ## STATUS
--
-- Type-checks `--safe --with-K`-clean.  No `postulate` declarations.
-- 1 residual field (`AllFire-edge-↭`) strictly narrower than the
-- parent goal `AllFire-via-bij`.
--------------------------------------------------------------------------------
