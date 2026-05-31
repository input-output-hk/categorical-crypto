{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- The TOPOLOGICAL FIRING-SUCCESS residual of `run-interchange-⟪⟫`.
--
-- ## What this file proves
--
-- The `SS.FrontSwap.RunInterchange` record (`Discharge/SwapStep.agda`) has
-- TWO fields:
--
--   reshuffle : pe-stack (e ∷ e' ∷ qs) sp  Perm.↭  pe-stack (e' ∷ e ∷ qs) sp
--   run-eq    : pe-term  (e' ∷ e ∷ qs) sp  ≈Term  permute … ∘ pe-term (e ∷ e' ∷ qs) sp
--
-- The `reshuffle` field is the TOPOLOGICAL FIRING-SUCCESS / stack-permutation
-- half: it asserts that running the two front edges in BOTH orders from the
-- shared post-prefix stack `sp` reaches `Perm.↭`-equal final stacks.  This is
-- EXACTLY the conclusion of
--
--   SV.PerHG.front-swap-stack-↭ H dih lin qs inc sp
--     : pe-stack (e ∷ e' ∷ qs) sp  Perm.↭  pe-stack (e' ∷ e ∷ qs) sp
--
-- (`Discharge/SwapValidity.agda`), which is FULLY PROVEN — no postulate —
-- from `Linear H` + `Incomp e e'`, via the firing-stability machinery
-- (`ein-ein-disjoint` from Linearity, `eout-ein-disjoint` from Incomp,
-- `e'-fires-stable` / `e'-skips-stable`, and `post-swap-stack-↭`).
--
-- The two `pe-stack`s coincide DEFINITIONALLY in `SwapStep` and `SwapValidity`
-- (both unfold to `proj₁ (process-edges H o s)`), and `Order`/`Incomp` are
-- shared (both derived from `IW.PerHG H dih`), so the transport is the
-- identity.
--
-- ## Status of the firing-success residual
--
-- FULLY DISCHARGED from `Linear H` (+ `Incomp`).  `front-swap-reshuffle`
-- below is the `reshuffle` field of `RunInterchange`, proven with no
-- postulate.  This is the residual the task asked to investigate: the
-- comments scattered in `Sub/AllFireEdgeSwap.agda` / `Sub/SwapAlreadyFires.agda`
-- claiming firing-success of both orders is FALSE on Linear inputs were
-- referring to a DIFFERENT (weaker, `Incomp`-free) formulation that was never
-- connected to `SwapValidity`'s `Linear`-based proof.  With `Incomp` (which
-- the consumer DOES have) + `Linear`, it is a theorem.
--
-- ## What is NOT proven here
--
-- The `run-eq` field (the term-level σ-naturality / Mac Lane interchange) is
-- the genuinely-hard residual and is OUT OF SCOPE — it is not a firing-success
-- fact.  This file isolates ONLY the firing-success/stack half.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FiringSwap
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.SwapValidity sig as SV

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Fin using (Fin)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (proj₁)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, the `Dep`-irreflexivity witness `dih`, and the
-- linearity proof `lin`.  These are exactly the inputs available at the
-- consumer's call site (`H = ⟪ f ⟫`).

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H) where

  private
    module H = Hypergraph H

  ------------------------------------------------------------------------
  -- The firing-success / stack-permutation half of `RunInterchange`.
  --
  -- This is the `reshuffle` field, proven from `Linear` + `Incomp` via
  -- `SwapValidity.PerHG.front-swap-stack-↭`.  Stated at EXACTLY the type
  -- the `RunInterchange.reshuffle` field expects (`SwapStep`'s `pe-stack`,
  -- which is definitionally `SwapValidity`'s).

  front-swap-reshuffle
    : ∀ (ps qs : SS.PerHG.Order H dih)
        {e e' : Fin H.nE}
        (inc : SS.PerHG.Incomp H dih e e')
    → SS.PerHG.pe-stack H dih (e ∷ e' ∷ qs) (SS.PerHG.pe-stack H dih ps H.dom)
      Perm.↭
      SS.PerHG.pe-stack H dih (e' ∷ e ∷ qs) (SS.PerHG.pe-stack H dih ps H.dom)
  front-swap-reshuffle ps qs {e} {e'} inc =
    SV.PerHG.front-swap-stack-↭ H dih lin qs inc
      (SV.PerHG.pe-stack H dih lin ps H.dom)
