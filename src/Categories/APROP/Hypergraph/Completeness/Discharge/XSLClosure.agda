{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Consolidation file: the maximal constructive chain toward
-- `X-permute-self-loop-id` (XSL).
--
-- The original (XSL) field in `DecodeRespIso.agda` is X-level and
-- UNCONDITIONAL.  It is FALSE in general — counter-example
-- `xs = [x, x]`, `r = swap x x refl` produces `permute r = σ ≢ id`.
--
-- The constructive ladder developed by sibling agents (A–D) reduces
-- the field to the strictly narrower residuals below, valid on MAPPED
-- LISTS (`map vlab is`) with `Unique is` and `InjectiveVlab vlab`:
--
--   * `Discharge/Sub/XToFinLift.agda`  (Agent A) — X-to-Fin lift.
--       Constructive: `↭-from-map`, `X-self-loop-lift-via-injective`,
--       `X-self-loop-id-on-mapped`.
--   * `Discharge/Sub/SelfLoopTransClosure.agda`  (Agent B) — 10/13
--       cases of `SelfLoopPostulate` via Acc-recursion on `size`.
--       Residual: `WithResidual.residual-handler`.
--   * `Discharge/Sub/SelfLoopTransClosed.agda`  (Agent C) — `right-assoc`
--       normalization infrastructure (not yet bundled here).
--   * `Discharge/Sub/SelfLoopFullClosure.agda`  (Agent D) — closes 11
--       of 13 cases via lex-Acc on `(size, total-l)` + `dnorm`.
--       Residual: `NormalFormHandler` for cases
--         (A)  `trans (prep _ _) (trans X Y)` in normal form, and
--         (B)  `trans (swap _ _ _) (trans X Y)` in normal form.
--       Closing these requires σ-block algebra at multiple levels
--       (~300 LOC) — see file header for the three suggested paths.
--
-- This file wires the chain together: given a `NormalFormHandler` +
-- `InjectiveVlab vlab` + `Unique is`, we derive the X-level self-loop
-- result constructively for any `r : map vlab is ↭ map vlab is`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.XSLClosure
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.XToFinLift sig-dec
  using (InjectiveVlab; X-self-loop-id-on-mapped)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (NormalFormHandler; module WithNormalFormHandler)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopNormalFormHandler sig-dec
  using (SigmaCascadeResidual; module WithSigmaResidual-SelfLoop)

--------------------------------------------------------------------------------
-- ## The deepest residual record.
--
-- After agent E's σ-cascade closure, the deepest known residual is
-- `SigmaCascadeResidual` — 6 fields, 3 of which are "dead branches"
-- (unreachable in practice from `self-loop-lex`) and 3 of which are
-- the GENUINE σ-cascade triples that require σ-block algebra:
--
--   * `A-swap` : `trans (prep _) (trans (swap _ _ _) Y) ≈Term id`.
--   * `B-prep` : `trans (swap _) (trans (prep _) Y) ≈Term id`.
--   * `B-swap` : `trans (swap _) (trans (swap _ _ _) Y) ≈Term id`.
--
-- These three are the irreducible Kelly content at the Fin level after
-- all `dnorm`, prep-fusion, and Unique-driven case analysis.

record XSLDeepestResidual : Set where
  field
    sigma-cascade-residual : SigmaCascadeResidual

--------------------------------------------------------------------------------
-- ## The deeper-narrowing residual record.
--
-- For consumers who don't want to engage with the σ-cascade
-- decomposition, the `NormalFormHandler` is exposed as an alternative
-- entry point.  Strictly less granular than `SigmaCascadeResidual`,
-- but more convenient as a single opaque postulate.

record XSLNarrowestResidual : Set where
  field
    -- Cases (A) and (B) of the lex-Acc residual after `dnorm`
    -- normalization.  Strictly narrower than the original (XSL):
    --   * Operates on Fin-level `↭` (already lifted from X-level).
    --   * Already has `Unique xs` precondition.
    --   * Already has `total-l p ≡ 0` (normal form) precondition.
    --   * Already has access to `Acc _≪_` and same-`xs` `self-rec`.
    normal-form-handler : NormalFormHandler

--------------------------------------------------------------------------------
-- ## The constructive chain (from `NormalFormHandler`).
--
-- Given the `NormalFormHandler` residual + `InjectiveVlab vlab` +
-- `Unique is`, derive the X-level self-loop on `map vlab is`.

module FromResidual (residual : XSLNarrowestResidual) where
  open XSLNarrowestResidual residual
  open WithNormalFormHandler normal-form-handler
    using (selfLoopPostulate)

  X-self-loop-on-mapped-id
    : ∀ {n} (vlab : Fin n → X)
        (inj : InjectiveVlab vlab)
        {is : List (Fin n)} (uniq : Unique is)
        (r : map vlab is Perm.↭ map vlab is)
    → permute r ≈Term id
  X-self-loop-on-mapped-id vlab inj uniq r =
    X-self-loop-id-on-mapped vlab inj selfLoopPostulate uniq r

--------------------------------------------------------------------------------
-- ## The constructive chain (from `SigmaCascadeResidual`).
--
-- A caller supplying the deepest residual gets a `NormalFormHandler`
-- via agent E's work, and thus the X-level self-loop on mapped lists.

module FromDeepest (residual : XSLDeepestResidual) where
  open XSLDeepestResidual residual
  open WithSigmaResidual-SelfLoop sigma-cascade-residual
    using (selfLoopPostulate)

  X-self-loop-on-mapped-id
    : ∀ {n} (vlab : Fin n → X)
        (inj : InjectiveVlab vlab)
        {is : List (Fin n)} (uniq : Unique is)
        (r : map vlab is Perm.↭ map vlab is)
    → permute r ≈Term id
  X-self-loop-on-mapped-id vlab inj uniq r =
    X-self-loop-id-on-mapped vlab inj selfLoopPostulate uniq r

--------------------------------------------------------------------------------
-- ## Trust-surface summary
--
-- After this chain, the trust surface for the (XSL) field in
-- `DecodeRespIso.agda` is:
--
--   * `XSLNarrowestResidual` (= `NormalFormHandler`) — STRICTLY
--     NARROWER than original (XSL).  Already at Fin-level, already
--     Unique, already normalized, already same-xs.
--   * `InjectiveVlab vlab` on the hypergraph's `vlab` — a STRUCTURAL
--     side-condition, not a categorical coherence claim.
--
-- The X-level claim itself (the FALSE-in-general original (XSL)) is
-- replaced with its restriction to MAPPED LISTS, which the
-- consumer's actual call sites already use.
--
-- ## Integration note
--
-- This file is NOT yet wired into `DecodeRespIso.CompletenessAssumptions`
-- because doing so requires refactoring `PermuteCoherenceShared.FromXSelfLoop`
-- (and its consumers `ProcessTermNew.WithAssumption` and
-- `FinalPermuteNew.WithCoherence`) to thread structural data through
-- the `permute-≈Term-coherence` call sites.  The structural data IS
-- available at the actual call sites (both sides of the (c)/(d)
-- discharges always use `map vlab _` lists), but extracting it
-- mechanically requires a non-trivial refactor.  This is left as
-- future work; the chain above is the maximal constructive content
-- currently available.
--------------------------------------------------------------------------------
