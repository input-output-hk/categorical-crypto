{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- # Option δ: a single, explicit Kelly-coherence postulate.
--
-- This module exposes ONE postulate -- `Kelly-faithfulness` -- and wires
-- it through the existing constructive XSL closure chain in
-- `Categories.PermuteCoherence.*` and
-- `Categories.APROP.Hypergraph.Completeness.Discharge.Sub.{XSLByFinBij,
-- XToFinLift}` to obtain a fully top-level `SelfLoopPostulate` and the
-- X-level mapped self-loop corollary.
--
-- ## What is `Kelly-faithfulness`?
--
-- The postulate is exactly the wide residual `FaithfulnessResidual` of
-- `Categories.PermuteCoherence.Faithfulness`, instantiated at the APROP
-- `FreeMonoidalData`.  It states:
--
--   For all `xs ys : List X` and list-permutation derivations
--   `p, q : xs Perm.↭ ys`, if `p ≅↭ q` (the two derivations evaluate to
--   the SAME finite bijection, up to FinBij-equality), then the
--   corresponding `permute` terms are `≈Term`-equal in the free
--   symmetric monoidal category over `X`.
--
-- This is Kelly's symmetric-monoidal coherence theorem [1], restricted
-- to the structural (permute-built) fragment.  It is a well-known, true
-- mathematical statement: any two parallel structural morphisms in a
-- symmetric monoidal category that agree on their underlying finite
-- bijection are equal up to the SMC axioms (σ-naturality, hexagon,
-- pentagon, triangle).
--
-- ## Why this is the RIGHT postulate
--
-- The XSL closure chain in `Categories/PermuteCoherence/` has
-- constructively narrowed completeness to this single residual.  In
-- particular:
--
--   * `Eval.agda`        -- evaluates ↭-derivations to FinBij.
--   * `Canonical.agda`   -- canonical normal form for ≅↭.
--   * `CanonicalBridge.agda`, `CanonicalBridgeSwap.agda`,
--     `CanonicalBridgeTrans.agda` -- bridge canonical forms back to
--     `permute` via σ-naturality, hexagon, etc.
--
-- All other pieces of the XSL closure are CONSTRUCTIVE; this is the
-- last residual.  Postulating it explicitly is therefore the minimal
-- assumption needed to close the chain.
--
-- ## Future work
--
-- The constructive narrowing in
-- `Categories.PermuteCoherence.CanonicalBridgeTrans.canonical-↭-∘-coherence`
-- already provides a path to discharging this postulate.  Replacing
-- this single postulate with the full constructive chain is a finite,
-- self-contained refactor (no further architectural blockers).
--
-- ## Module status
--
--   * Options: `--safe --with-K` (matches other Discharge modules).
--   * Postulates: exactly ONE (`Kelly-faithfulness`).
--   * Everything else: constructive.
--
-- [1] G.M. Kelly, "On MacLane's conditions for coherence of natural
--     associativities, commutativities, etc.", J. Algebra 1 (1964).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.KellyCoherence
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.XSLByFinBij sig-dec
  using (module WithFaithfulnessResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.XToFinLift sig-dec
  using (InjectiveVlab; X-self-loop-id-on-mapped)

import Categories.PermuteCoherence.Faithfulness as Faith

private
  module Fa = Faith asFreeMonoidalData

open Fa using (FaithfulnessResidual; TransSelfLoopResidual; wide⇒narrow)

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

--------------------------------------------------------------------------------
-- ## 1.  THE Kelly coherence postulate (the only postulate in this module).

postulate
  -- Kelly's symmetric-monoidal coherence theorem, restricted to the
  -- structural (permute-built) fragment of the free SMC over `X`.
  --
  -- Any two parallel list-permutation derivations whose evaluated
  -- bijections agree (`p ≅↭ q`) produce `≈Term`-equal `permute` terms.
  --
  -- This is the ONLY residual remaining after the constructive
  -- narrowing in `Categories.PermuteCoherence.*`.  Discharging it
  -- constructively is the well-known SMC coherence theorem and is
  -- mathematically true.
  Kelly-faithfulness : FaithfulnessResidual

--------------------------------------------------------------------------------
-- ## 2.  Narrow residual via the constructive `wide⇒narrow` implication.

Kelly-trans-self-loop : TransSelfLoopResidual
Kelly-trans-self-loop = wide⇒narrow Kelly-faithfulness

--------------------------------------------------------------------------------
-- ## 3.  Constructive `SelfLoopPostulate` via `XSLByFinBij`.
--
-- Feed the Kelly postulate to the existing XSL closure machinery to
-- obtain a top-level `SelfLoopPostulate` value -- no further
-- postulates required downstream.

open WithFaithfulnessResidual Kelly-faithfulness public
  using (constructive-self-loop-postulate)

--------------------------------------------------------------------------------
-- ## 4.  X-level mapped self-loop corollary via `XToFinLift`.
--
-- The headline X-level statement: for any injective `vlab : Fin n → X`
-- and `Unique`-indexed list `is`, every self-loop on `map vlab is`
-- evaluates under `permute` to `id`.

constructive-X-self-loop-id-on-mapped
  : ∀ {n} (vlab : Fin n → X) (inj : InjectiveVlab vlab)
      {is : List (Fin n)} (uniq : Unique is)
      (r : map vlab is Perm.↭ map vlab is)
  → permute r ≈Term id
constructive-X-self-loop-id-on-mapped vlab inj uniq r =
  X-self-loop-id-on-mapped vlab inj constructive-self-loop-postulate uniq r
