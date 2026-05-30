-- Discharge of the `swap-validity` postulate of `IsoInvarianceWiring.agda`'s
-- `PerHG` module (§(II) of the informal completeness proof).
--
--   swap-validity : ∀ {o₁ o₂} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
--
-- where `Valid o = proj₁ (process-edges H o dom) Perm.↭ cod` and a step
-- `o₁ ↝ o₂` is `swap-step ps qs (inc : Incomp (Dep H) e e')` swapping an
-- adjacent `Dep`-incomparable pair after a prefix `ps`.
--
-- ## Route (WiringLemmas.agda Lemma 1)
--
-- The final live-wire multiset (`finalStack o = proj₁ (process-edges o dom)`)
-- is order-independent for a swap of `Dep`-incomparable adjacent edges.
-- Concretely we prove
--
--   finalStack-↭ : finalStack o₁  Perm.↭  finalStack o₂
--
-- and then transport `Valid` by
--
--   Valid o₂  =  ↭-trans (↭-sym finalStack-↭) (Valid o₁).
--
-- ## Decomposition
--
--   (1) `++-stack` (= `process-edges-++-stack`, imported, REAL): the final
--       stack of `ps ++ rest` from `dom` is that of `rest` from the
--       post-`ps` stack `sp = pe-stack ps dom`.  This reduces the general
--       swap to a FRONT swap (`ps = []`) on the shared post-prefix stack.
--
--   (2) `front-swap-stack-↭` — the front-of-stack two-edge stack
--       permutation, for `Dep`-INCOMPARABLE `e , e'`.  This is the analytic
--       core: independence (`Incomp`: neither edge shares a wire with the
--       other) makes `edge-step e ; edge-step e'` reach the same final-stack
--       MULTISET as the reverse order.  The disjoint-stack multiset content
--       is exactly `Sub/AllFireEdgeSwap.post-swap-stack-↭`; bridging the
--       `process-edges`/`edge-step` representation (which may SKIP an edge
--       whose `ein` is not a sub-multiset of the stack) to the four-AllFire
--       hypotheses of that lemma requires the `extract-prefix`-failure-is-
--       stable-under-disjoint-additions bookkeeping.  Isolated here as a
--       single clearly-marked TODO postulate (mirrors how `SwapStep.agda`
--       isolates `front-swap-≈`).  TRUE (bookkeeping only), no analytic
--       content beyond the multiset reasoning already in `AllFireEdgeSwap`.
--
--   (3) `swap-validity` — assembled from (1) + (2) + `Perm.↭`-transitivity.
{-# OPTIONS --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.SwapValidity
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step)

-- The chain we discharge against, imported read-only: `PH.Valid`, `PH.↝`,
-- `PH.Order`, and the LinExt instantiation (`Incomp`, `swap-step`).
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (process-edges-++-stack)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H` and a `Dep`-irreflexivity witness `dih`, and
-- open the existing `PerHG` machinery.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H

  -- The existing per-hypergraph module from the chain (read-only).  We
  -- match its `Order`, `Valid`, `_↝_` definitionally so the result can
  -- replace the postulate verbatim.
  module PH = IW.PerHG H dih

  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)` and the swap-step
  -- constructor, both from the LinExt instantiation `PH.L`.
  open PH.L public using (Incomp; swap-step)

  ------------------------------------------------------------------------
  -- The final stack of running an order from a stack.
  ------------------------------------------------------------------------

  -- `finalStack o = proj₁ (process-edges o dom)` (the `Valid`-relevant
  -- projection); generalised here to an arbitrary starting stack `s`.
  pe-stack : PH.Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  finalStack : PH.Order → List (Fin H.nV)
  finalStack o = pe-stack o H.dom

  -- The stack `_++_`-factoring (imported, REAL): the final stack of
  -- `ps ++ rest` from `s` is that of `rest` from the post-`ps` stack.
  ++-stack
    : ∀ (ps rest : PH.Order) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  ++-stack = process-edges-++-stack H

  ------------------------------------------------------------------------
  -- (2) THE ANALYTIC CORE — front-of-stack two-edge stack permutation.
  --
  -- For `Dep`-INCOMPARABLE `e , e'` (neither produces a wire the other
  -- consumes), running `e ∷ e' ∷ qs` from a stack `s` reaches a final
  -- stack that is a `Perm.↭`-permutation of the one reached by running
  -- the swapped order `e' ∷ e ∷ qs` from `s`.
  --
  -- TRUE (bookkeeping only): the disjoint-stack multiset content is
  -- `Sub/AllFireEdgeSwap.post-swap-stack-↭`.  The residual content is the
  -- representation bridge between `edge-step` (which SKIPS an edge whose
  -- `ein` is not a sub-multiset of the stack, leaving the stack unchanged)
  -- and the four-AllFire hypotheses of `post-swap-stack-↭`: under `Incomp`
  -- the firing/non-firing status of each edge is the SAME in both orders
  -- (the wires the other edge adds/removes are disjoint from this edge's
  -- `ein`), and when both fire the residual perms line up.  Reducing the
  -- `with extract-prefix …` case split to those perms is `extract-prefix`-
  -- membership bookkeeping; isolated as a single TODO postulate.
  ------------------------------------------------------------------------

  postulate
    -- TODO: constructive proof.  Case-split `edge-step s e` /
    -- `edge-step _ e'` (and the swapped order) on the four
    -- `extract-prefix` outcomes; under `Incomp` the fire/skip status of
    -- each edge agrees across the two orders (disjoint-wire stability of
    -- `extract-prefix` success/failure), and the both-fire case is closed
    -- by `Sub/AllFireEdgeSwap.post-swap-stack-↭` after threading the
    -- residual perms through `process-edges qs`.  ~300–500 LOC of
    -- `extract-prefix` / multiset reasoning.
    front-swap-stack-↭
      : ∀ (qs : PH.Order) {e e' : Fin H.nE}
          (inc : Incomp e e') (s : List (Fin H.nV))
      → pe-stack (e ∷ e' ∷ qs) s  Perm.↭  pe-stack (e' ∷ e ∷ qs) s

  ------------------------------------------------------------------------
  -- (general swap) `finalStack`-↭ for a swap after an arbitrary prefix.
  --
  -- Reduce to the front swap via `++-stack`, then apply
  -- `front-swap-stack-↭` at the shared post-prefix stack.
  ------------------------------------------------------------------------

  swap-stack-↭
    : ∀ (ps qs : PH.Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → pe-stack (ps ++ e ∷ e' ∷ qs) H.dom
      Perm.↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom
  swap-stack-↭ ps qs {e} {e'} inc =
    subst (Perm._↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom)
          (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
      (subst (pe-stack (e ∷ e' ∷ qs) (pe-stack ps H.dom) Perm.↭_)
             (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
        (front-swap-stack-↭ qs inc (pe-stack ps H.dom)))

  ------------------------------------------------------------------------
  -- (3) `swap-validity`: transport `Valid` along `swap-stack-↭`.
  --
  --   Valid o = finalStack o Perm.↭ cod
  --
  -- so `Valid o₂ = ↭-trans (↭-sym (finalStack o₁ ↭ finalStack o₂))
  --                        (Valid o₁)`.
  ------------------------------------------------------------------------

  swap-validity : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂ → PH.Valid o₁ → PH.Valid o₂
  swap-validity (swap-step ps qs inc) p₁ =
    Perm.↭-trans (Perm.↭-sym (swap-stack-↭ ps qs inc)) p₁
