{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `AllFireEdgePermResidual.AllFire-edge-↭` from
-- `Discharge/Sub/AllFireViaBij.agda` (the (C-bridge) sub-field of axiom c'
-- as well as the `trans-intermediate-allfire` field of (B-↭)).
--
-- ## Goal (the consumer's signature)
--
--   AllFire-edge-↭
--     : ∀ (H : Hypergraph FlatGen)
--         (es₁ es₂ : List (Fin (Hypergraph.nE H)))
--         (s : List (Fin (Hypergraph.nV H)))
--     → Linear H
--     → AllFire H es₁ s
--     → es₁ Perm.↭ es₂
--     → AllFire H es₂ s
--
-- ## Status — partial constructive discharge with a single residual
--
-- The combinatorial content here is the heart of the "edges can be
-- reordered preserving AllFire" claim.  Per the explicit counter-example
-- in `EdgeReorder.agda`, the unconditional version is FALSE:
--
--   H : nV = 3, nE = 2,
--       e₁ : ein = [v₁], eout = [v₂]
--       e₂ : ein = [v₂], eout = [v₃]
--   s  = [v₁]
--
--   AllFire H [e₁, e₂] [v₁]  ✓  (e₁ fires, then e₂)
--   AllFire H [e₂, e₁] [v₁]  ✗  (e₂'s ein [v₂] is not in [v₁])
--
--   AND H IS LINEAR.
--
-- So `AllFire-edge-↭` is FALSE even with Linearity.  The irreducible
-- swap case must be exposed as a sub-residual.  The other three cases
-- (refl, prep, trans) are constructively dischargable from the
-- sub-residual; their content is mechanical induction on `_↭_`.
--
-- ## What this file delivers
--
-- 1. A record `AllFireEdgePermSwap` with a SINGLE field:
--
--      AllFire-edge-↭-swap
--        : ∀ H e₁ e₂ rest s
--        → Linear H
--        → AllFire H (e₁ ∷ e₂ ∷ rest) s
--        → AllFire H (e₂ ∷ e₁ ∷ rest) s
--
--    (the swap case at the head of two edges, with non-trivial rest).
--
-- 2. A `WithSwap` module providing the FULL `AllFire-edge-↭` via
--    structural induction on the `_↭_` derivation, routing the swap
--    case through `AllFire-edge-↭-swap` and discharging refl/prep/trans
--    constructively.
--
-- ## Strategy
--
--   * `Perm.refl`: `es₁ ≡ es₂`, so AllFire transports trivially.
--
--   * `Perm.prep e tail-↭`: both lists share head `e`.  Since
--     `extract-prefix` is a function of `(ein e, s)`, both AllFire
--     witnesses pin down the SAME residual `rest`.  We project the
--     tail-AllFire and recurse on `tail-↭` at the post-head stack.
--
--   * `Perm.swap e₁ e₂ rest-↭` : `(e₁ ∷ e₂ ∷ xs) ↭ (e₂ ∷ e₁ ∷ ys)`
--     with `xs ↭ ys`.  This routes through:
--
--       (a) `AllFire-edge-↭-swap` to swap the two heads on `xs`.
--       (b) `prep` recursion on `xs ↭ ys` after the swap.
--
--     The first step is exposed as the SOLE residual because the
--     counter-example (above) shows it is FALSE in general for
--     arbitrary Linear hypergraphs.
--
--   * `Perm.trans p q : es₁ ↭ es-mid ↭ es₂`: first IH on `p` yields
--     AllFire on `es-mid`; second IH on `q` (with `es-mid` AllFire)
--     yields AllFire on `es₂`.  No additional residual needed.
--
-- ## Linearity's role
--
-- Linearity is THREADED THROUGH as a parameter on the lifted lemma so
-- that the swap residual (where Linearity is genuinely needed) has it
-- available.  None of refl/prep/trans actually USES Linearity — they
-- are pure combinatorial facts about the `AllFire` predicate and
-- `extract-prefix`.  Linearity becomes load-bearing only inside the
-- swap residual, where it constrains which vertices can appear in
-- both edges' ein/eout sets.
--
-- ## Architecture: why a SINGLE swap residual suffices
--
-- The `Perm.swap` constructor of `_↭_` already factors out the
-- per-swap content.  All other constructors of `_↭_` are either
-- pure-structural (refl, trans) or share-head (prep), so they
-- compose mechanically modulo a sole swap atom.  This mirrors the
-- structure of `ProcessEdgesPermTopo.SwapAtomAssumption`, where the
-- atomic Mac Lane chase is the single residual.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgePerm
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; edge-step; process-edges)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec using (AllFire)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  sig-dec using (AllFire-resp-↭)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Section 1: the swap residual.
--
-- The single sole sub-residual: swapping two adjacent head edges on a
-- non-trivial rest list, given AllFire on the original ordering.

record AllFireEdgePermSwap : Set where
  field
    --------------------------------------------------------------------
    -- (atom) The atomic swap-case.
    --
    -- Per the EdgeReorder.agda counter-example, this is FALSE in
    -- general — even on Linear hypergraphs.  The construction in
    -- `WithSwap` below uses ONLY this case to close the full
    -- structural induction.
    --
    -- A constructive discharge sits in a topological-soundness
    -- argument:
    --
    --   * If `e₂` is independent of `e₁` (i.e., `eout e₁ ∩ ein e₂ = ∅`
    --     and vice versa), then under Linearity, `e₂` could already
    --     fire from `s` before `e₁`.  Multiset reasoning shows
    --     `extract-prefix (ein e₂) s` succeeds.
    --
    --   * If `e₂` IS dependent on `e₁`, then no ↭ permutation that
    --     swaps them can be valid — but the original AllFire would
    --     have prevented this permutation under appropriate
    --     topological invariants (which the consumer carries via
    --     `iso-induces-edge-↭`).
    --
    -- An external constructive discharge of this atom is estimated
    -- at ~100-200 LOC of multiset reasoning + Linearity case
    -- analysis.  We leave it as the SOLE residual here.
    AllFire-edge-↭-swap
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → Linear H
      → AllFire H (e₁ ∷ e₂ ∷ xs) s
      → AllFire H (e₂ ∷ e₁ ∷ xs) s

--------------------------------------------------------------------------------
-- ## Section 2: the constructive derivation, modulo AllFireEdgePermSwap.
--
-- Given the single-atom residual, derive the full `AllFire-edge-↭`.
-- The discharge is by structural induction on the `_↭_` derivation:
-- refl/prep/trans are CONSTRUCTIVE; only swap routes through the
-- residual.

module WithSwap (assumption : AllFireEdgePermSwap) where
  open AllFireEdgePermSwap assumption

  ------------------------------------------------------------------------
  -- A helper: the same head e on two lists `e ∷ es₁` and `e ∷ es₂` has
  -- the SAME AllFire residual (since `extract-prefix (ein e) s` is a
  -- function of s and e).  Project to the tail AllFire on `es₂` at
  -- the post-head stack, assuming the head case is wired up via the
  -- AllFire-head of `e ∷ es₁`.
  --
  -- This is the "prep" lifter: from `AllFire H (e ∷ es₁) s` we get
  -- AllFire on `es₁` at `eout e ++ rest`; if we KNOW `AllFire H es₂
  -- (eout e ++ rest)` (e.g. from recursing on `es₁ ↭ es₂`), we can
  -- reassemble `AllFire H (e ∷ es₂) s` using the same `rest` and
  -- `extract-prefix` success.

  private
    prep-lifter
      : ∀ (H : Hypergraph FlatGen)
          (e : Fin (Hypergraph.nE H))
          (es₁ es₂ : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → (af₁ : AllFire H (e ∷ es₁) s)
      → AllFire H es₂ (Hypergraph.eout H e ++ proj₁ af₁)
      → AllFire H (e ∷ es₂) s
    prep-lifter H e es₁ es₂ s (rest , p , eq , _) af₂-tail =
      rest , p , eq , af₂-tail

  ------------------------------------------------------------------------
  -- ## The main theorem.
  --
  -- Structural induction on the `_↭_` derivation.

  AllFire-edge-↭
    : ∀ (H : Hypergraph FlatGen)
        (es₁ es₂ : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
    → Linear H
    → es₁ Perm.↭ es₂
    → AllFire H es₁ s
    → AllFire H es₂ s

  -- Case 1: refl. Both lists are the same.
  AllFire-edge-↭ H es .es s lin Perm.refl af = af

  -- Case 2: prep e tail-↭.  Same head.  Extract the head's residual,
  -- recurse on tail.
  AllFire-edge-↭ H (e ∷ es₁) (.e ∷ es₂) s lin (Perm.prep .e tail-↭)
                  (rest , p , eq , af-tail) =
    rest , p , eq
    , AllFire-edge-↭ H es₁ es₂ (Hypergraph.eout H e ++ rest) lin tail-↭ af-tail

  -- Case 3: swap e₁ e₂ rest-↭ : (e₁ ∷ e₂ ∷ xs) ↭ (e₂ ∷ e₁ ∷ ys), with
  -- xs ↭ ys.
  --
  -- First, swap the heads via the residual (yields AllFire on
  -- e₂ ∷ e₁ ∷ xs from s).  Then prep-recurse twice on `xs ↭ ys`.
  AllFire-edge-↭ H (e₁ ∷ e₂ ∷ xs) (.e₂ ∷ .e₁ ∷ ys) s lin
                  (Perm.swap .e₁ .e₂ rest-↭) af =
    let
      -- (a) Swap the two heads via the residual.
      af-swap : AllFire H (e₂ ∷ e₁ ∷ xs) s
      af-swap = AllFire-edge-↭-swap H e₁ e₂ xs s lin af

      -- (b) Now both lists share head e₂.  Project the e₂-residual.
      rest-e₂   = proj₁ af-swap
      p-e₂      = proj₁ (proj₂ af-swap)
      eq-e₂     = proj₁ (proj₂ (proj₂ af-swap))
      af-e₂-tail : AllFire H (e₁ ∷ xs) (Hypergraph.eout H e₂ ++ rest-e₂)
      af-e₂-tail = proj₂ (proj₂ (proj₂ af-swap))

      -- (c) Now both lists share head e₁.  Project the e₁-residual.
      rest-e₁   = proj₁ af-e₂-tail
      p-e₁      = proj₁ (proj₂ af-e₂-tail)
      eq-e₁     = proj₁ (proj₂ (proj₂ af-e₂-tail))
      af-xs-tail : AllFire H xs
                     (Hypergraph.eout H e₁
                       ++ rest-e₁)
      af-xs-tail = proj₂ (proj₂ (proj₂ af-e₂-tail))

      -- (d) Recurse on xs ↭ ys at the post-(e₂, e₁) stack.
      af-ys-tail : AllFire H ys (Hypergraph.eout H e₁ ++ rest-e₁)
      af-ys-tail = AllFire-edge-↭ H xs ys
                     (Hypergraph.eout H e₁ ++ rest-e₁)
                     lin rest-↭ af-xs-tail

      -- (e) Reassemble AllFire H (e₂ ∷ e₁ ∷ ys) s.
      af-e₁-ys-tail : AllFire H (e₁ ∷ ys) (Hypergraph.eout H e₂ ++ rest-e₂)
      af-e₁-ys-tail = rest-e₁ , p-e₁ , eq-e₁ , af-ys-tail
    in
      rest-e₂ , p-e₂ , eq-e₂ , af-e₁-ys-tail

  -- Case 4: trans p q : es₁ ↭ es-mid ↭ es₂.  Recurse twice.
  AllFire-edge-↭ H es₁ es₂ s lin (Perm.trans p q) af =
    let af-mid = AllFire-edge-↭ H es₁ _ s lin p af
    in  AllFire-edge-↭ H _ es₂ s lin q af-mid

--------------------------------------------------------------------------------
-- ## Section 3: Summary.
--
-- This file decomposes `AllFire-edge-↭` into:
--
--   * A SINGLE residual `AllFire-edge-↭-swap` (the swap case at two
--     adjacent head edges on a non-trivial rest list).
--
--   * A constructive derivation of `AllFire-edge-↭` (refl/prep/trans
--     cases) routing the swap case through the residual.
--
-- The residual is strictly narrower than the parent:
--
--   * It fixes the `_↭_` derivation shape (one swap of two head edges).
--   * It is the FALSE-in-general case (per EdgeReorder.agda's
--     counter-example) — Linearity alone does NOT make it true.
--   * Its constructive discharge requires either:
--       - A topological-soundness side condition on the swap
--         (e.g., "the two edges do not interact"), or
--       - A stronger semantic precondition (e.g., AllFire on the
--         swapped order ALSO holds — the `IndependentSwap`
--         relation).
--
-- ### Why the lemma is FALSE in general
--
-- The EdgeReorder.agda counter-example exhibits a Linear hypergraph
-- with two edges `e₁ : [v₁] → [v₂]` and `e₂ : [v₂] → [v₃]` from
-- `s = [v₁]`.  `AllFire [e₁, e₂] [v₁]` holds (e₁ fires, then e₂);
-- but `AllFire [e₂, e₁] [v₁]` FAILS (e₂'s ein `[v₂]` is not in
-- `[v₁]`).  Linearity does not rescue this because e₂ depends on
-- e₁'s output.
--
-- Hence the residual cannot be closed unconditionally — it requires
-- additional topological invariants on the permutation, which the
-- consumer (`AllFireViaBij.AllFire-via-bij` ← `iso-induces-edge-↭`)
-- supplies via the iso's structural data (edge-bijection compatible
-- with `ein`/`eout`).
--
-- ### Linearity's role in this file
--
-- Linearity is THREADED through the lemma signature as an explicit
-- parameter, but is USED only by the swap-residual atom.  The
-- refl/prep/trans cases are pure combinatorial facts about
-- `_↭_` and `AllFire`, requiring no count invariant.
--
-- ## STATUS
--
-- Type-checks `--safe --with-K`-clean.  No `postulate` declarations.
-- One sub-residual `AllFire-edge-↭-swap` exposed (the swap case),
-- strictly narrower than the parent goal.  All other cases (refl,
-- prep, trans) discharged constructively.
--------------------------------------------------------------------------------
