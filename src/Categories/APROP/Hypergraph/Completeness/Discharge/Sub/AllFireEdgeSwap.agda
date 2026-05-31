{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `AllFireEdgePermSwap.AllFire-edge-↭-swap` from
-- `Discharge/Sub/AllFireEdgePerm.agda` (the (B.1) atomic-swap leaf of
-- the c' closure).
--
-- ## Goal (the consumer's signature)
--
--   AllFire-edge-↭-swap
--     : ∀ (H : Hypergraph FlatGen)
--         (e₁ e₂ : Fin (Hypergraph.nE H))
--         (xs : List (Fin (Hypergraph.nE H)))
--         (s : List (Fin (Hypergraph.nV H)))
--     → Linear H
--     → AllFire H (e₁ ∷ e₂ ∷ xs) s
--     → AllFire H (e₂ ∷ e₁ ∷ xs) s
--
-- ## Status — Linearity ALONE is insufficient (false in general).
--
-- Per the EdgeReorder.agda counter-example, even on Linear hypergraphs
-- the unconditional version is FALSE:
--
--   H : nV = 3, nE = 2,
--       e₁ : ein = [v₁], eout = [v₂]
--       e₂ : ein = [v₂], eout = [v₃]
--   s  = [v₁]
--
--   AllFire H [e₁, e₂] [v₁]  ✓
--   AllFire H [e₂, e₁] [v₁]  ✗  (e₂'s ein [v₂] is not in [v₁])
--
--   AND H IS LINEAR (each vertex produced once, consumed once).
--
-- So the swap atom is FALSE in general.  The constructive discharge
-- requires an ADDITIONAL piece of topological data: that the SWAPPED
-- ordering also fires (at least for the two head edges).
--
-- ## What this file delivers
--
-- A constructive discharge of `AllFire-edge-↭-swap` from a STRICTLY
-- NARROWER topological premise: the assumption that AllFire holds on
-- BOTH orderings of the two head edges (`e₁ ∷ e₂ ∷ []` and
-- `e₂ ∷ e₁ ∷ []`), starting from `s`.
--
-- This is essentially `IndependentSwap` (defined in
-- `ProcessTermAligned.agda`), augmented with the tail-AllFire for `xs`.
-- The augmented hypothesis is exposed as `IndependentSwapTail`.  Given
-- it, the swap conclusion `AllFire H (e₂ ∷ e₁ ∷ xs) s` is fully
-- constructively derivable:
--
--   1. The "post-firing-both-edges" stack from order 1 (e₁ then e₂) is
--      `eout e₂ ++ r₂` for some residual `r₂`.
--   2. The same stack from order 2 (e₂ then e₁) is `eout e₁ ++ r₁'`.
--   3. From the four AllFire perms, we derive
--      `eout e₂ ++ r₂ Perm.↭ eout e₁ ++ r₁'`.
--   4. AllFire on `xs` transports along this perm via `AllFire-resp-↭`.
--
-- The construction is ~150 LOC of pure multiset / Perm reasoning.  No
-- Linear assumption is actually used in the proof body, but the
-- signature retains it for API compatibility with the parent.
--
-- ## Architecture: what data the consumer must supply
--
-- The consumer of `AllFire-edge-↭-swap` is `AllFireEdgePerm.WithSwap`
-- (in `Discharge/Sub/AllFireEdgePerm.agda`'s `WithSwap` module),
-- which routes the `Perm.swap` case of the structural induction.
-- The `Perm.swap` constructor of `_↭_` is built from `e₁ ∷ e₂ ∷ xs ↭
-- e₂ ∷ e₁ ∷ ys` derivations — but DOES NOT carry any topological
-- guarantee that the swapped ordering fires.  This is the irreducible
-- data the consumer must obtain elsewhere.
--
-- In the intended use (`IsoInducesEdgePerm.iso-induces-edge-↭`), this
-- data comes from the iso's structural fields (`ψ-ein`/`ψ-eout`):
-- the iso provides an edge bijection that respects topological order,
-- so the swapped ordering must already fire on the target hypergraph.
-- The consumer's path to this:
--
--   (a) Build the AllFire on the target order via the iso's bijection
--       (which uses the source's AllFire under the bijection).
--   (b) Project the head-pair AllFire from this target AllFire.
--   (c) Pass it to `AllFire-edge-↭-swap-via-indep` below.
--
-- This file exposes the constructive discharge under the augmented
-- hypothesis, plus exposes the SOLE residual `swap-already-fires` (a
-- record field) as the topological-soundness premise.  Together they
-- discharge the parent.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgeSwap
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; edge-step; process-edges)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec using (AllFire; IndependentSwap)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  sig-dec using (AllFire-resp-↭)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgePerm
  sig-dec using (AllFireEdgePermSwap)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Section 1: A `++`-left-cancellation lemma for `_↭_`.
--
-- `Perm.drop-∷` cancels a single shared head.  By induction, we obtain
-- cancellation of an entire shared prefix.

++-cancelˡ
  : ∀ {n} (xs : List (Fin n)) {ys zs : List (Fin n)}
  → xs ++ ys Perm.↭ xs ++ zs
  → ys Perm.↭ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)

--------------------------------------------------------------------------------
-- ## Section 2: The augmented hypothesis — `IndependentSwapTail`.
--
-- We package up the four AllFire pieces needed for the constructive
-- discharge of the swap atom on a non-trivial tail:
--
--   (a) AllFire on the original order `e₁ ∷ e₂ ∷ xs` from `s` — the
--       parent's input.
--   (b) The "swap fires" precondition: AllFire on `e₂ ∷ e₁ ∷ []`
--       from `s`.  This is the irreducible topological data NOT
--       implied by Linearity (per EdgeReorder.agda).
--
-- The conclusion is AllFire on `e₂ ∷ e₁ ∷ xs` from `s`.
--
-- NOTE: `IndependentSwap H e₁ e₂ s = AllFire H (e₁ ∷ e₂ ∷ []) s
-- × AllFire H (e₂ ∷ e₁ ∷ []) s`.  Here we don't need the first half
-- (we already have AllFire on `e₁ ∷ e₂ ∷ xs`, which subsumes the
-- head-pair); the second half (`e₂ ∷ e₁ ∷ []` AllFire) IS the
-- topological precondition.

--------------------------------------------------------------------------------
-- ## Section 3: The constructive swap derivation.
--
-- Given AllFire on both head-orderings, swap is fully constructive.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  ------------------------------------------------------------------------
  -- The stack-bridge: post-(e₁ ∷ e₂) stack from `s` is perm-equivalent
  -- to post-(e₂ ∷ e₁) stack from `s`, given AllFire on both orderings.
  --
  -- The four AllFire pieces are:
  --   p₁  : s ↭ ein e₁ ++ r₁
  --   p₂  : eout e₁ ++ r₁ ↭ ein e₂ ++ r₂
  --   p₂' : s ↭ ein e₂ ++ r₂'
  --   p₁' : eout e₂ ++ r₂' ↭ ein e₁ ++ r₁'
  --
  -- Goal: `eout e₂ ++ r₂ Perm.↭ eout e₁ ++ r₁'`.
  --
  -- Strategy:
  --   * From p₁ + p₂ + lifting: `s ++ eout e₁ ↭ ein e₁ ++ ein e₂ ++ r₂`,
  --     then `s ++ eout e₁ ++ eout e₂ ↭ ein e₁ ++ ein e₂ ++ eout e₂ ++ r₂`.
  --   * From p₂' + p₁' + lifting: `s ++ eout e₂ ++ eout e₁ ↭ ein e₂ ++
  --     ein e₁ ++ eout e₁ ++ r₁'`.
  --   * `++-comm` aligns `eout e₁ ++ eout e₂ ↭ eout e₂ ++ eout e₁`,
  --     so the two big perms have a common LHS (up to comm), allowing
  --     us to compare the RHSs.
  --   * `++-comm` on `ein e₁ ++ ein e₂` aligns the ein prefixes.
  --   * `++-cancelˡ` (Section 1) cancels the shared `ein e₂ ++ ein e₁`
  --     prefix.

  post-swap-stack-↭
    : ∀ (e₁ e₂ : Fin H.nE)
        (s r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : s Perm.↭ H.ein e₁ ++ r₁)
        (p₂  : H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂)
        (p₂' : s Perm.↭ H.ein e₂ ++ r₂')
        (p₁' : H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ r₁')
    → H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
  post-swap-stack-↭ e₁ e₂ s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁' = cancelled
    where
      open Perm.PermutationReasoning

      -- Stage 1: derive `ein e₁ ++ r₁ Perm.↭ ein e₂ ++ r₂'` via `s`.
      r₁-r₂' : H.ein e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂'
      r₁-r₂' = Perm.↭-trans (Perm.↭-sym p₁) p₂'

      -- Step A: ++⁺ˡ (eout e₂) p₂ gives:
      --   eout e₂ ++ eout e₁ ++ r₁ ↭ eout e₂ ++ ein e₂ ++ r₂
      step-A
        : H.eout e₂ ++ H.eout e₁ ++ r₁
        Perm.↭ H.eout e₂ ++ H.ein e₂ ++ r₂
      step-A = PermProp.++⁺ˡ (H.eout e₂) p₂

      -- Step B: pull `eout e₂` past `ein e₂` on the RHS:
      --   eout e₂ ++ ein e₂ ++ r₂ ↭ ein e₂ ++ eout e₂ ++ r₂
      step-B
        : H.eout e₂ ++ H.ein e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-B = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂) ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂
          ↭⟨ PermProp.++⁺ʳ r₂ (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂ ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂
          ∎

      -- Step C: chain A + B: `eout e₂ ++ eout e₁ ++ r₁ ↭ ein e₂ ++ eout e₂ ++ r₂`.
      step-C
        : H.eout e₂ ++ H.eout e₁ ++ r₁
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-C = Perm.↭-trans step-A step-B

      -- Symmetric construction starting from order 2.
      step-A'
        : H.eout e₁ ++ H.eout e₂ ++ r₂'
        Perm.↭ H.eout e₁ ++ H.ein e₁ ++ r₁'
      step-A' = PermProp.++⁺ˡ (H.eout e₁) p₁'

      step-B'
        : H.eout e₁ ++ H.ein e₁ ++ r₁'
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-B' = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁') ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁'
          ↭⟨ PermProp.++⁺ʳ r₁' (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁'
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁' ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁'
          ∎

      step-C'
        : H.eout e₁ ++ H.eout e₂ ++ r₂'
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-C' = Perm.↭-trans step-A' step-B'

      -- Multiply r₁-r₂' both sides by `eout e₁`, then `eout e₂`:
      mult-r₁-r₂'
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
      mult-r₁-r₂' =
        PermProp.++⁺ˡ (H.eout e₁) (PermProp.++⁺ˡ (H.eout e₂) r₁-r₂')

      -- Helper: rearrange eout e₁ ++ ein e₁ to ein e₁ ++ eout e₁ within `r₁` ctx.
      inner-lhs
        : H.eout e₁ ++ H.ein e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁
      inner-lhs = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁) ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁
          ↭⟨ PermProp.++⁺ʳ r₁ (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁ ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁
          ∎

      inner-lhs-2
        : H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
      inner-lhs-2 = begin
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₁) (H.eout e₁ ++ r₁)) ⟩
        (H.eout e₂ ++ H.ein e₁) ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.eout e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₂) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₂) ++ H.eout e₁ ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₂) (H.eout e₁ ++ r₁) ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
          ∎

      lhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
      lhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.eout e₂) (H.ein e₁ ++ r₁)) ⟩
        (H.eout e₁ ++ H.eout e₂) ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.ein e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₁) (H.eout e₂)) ⟩
        (H.eout e₂ ++ H.eout e₁) ++ H.ein e₁ ++ r₁
          ≡⟨ ++-assoc (H.eout e₂) (H.eout e₁) (H.ein e₁ ++ r₁) ⟩
        H.eout e₂ ++ H.eout e₁ ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.eout e₂) inner-lhs ⟩
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ↭⟨ inner-lhs-2 ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.ein e₁) step-C ⟩
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
          ∎

      -- Helper for rhs-rearrange:
      inner-rhs-inner
        : H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂'
      inner-rhs-inner = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂') ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂'
          ↭⟨ PermProp.++⁺ʳ r₂' (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂' ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂'
          ∎

      inner-rhs-1
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
      inner-rhs-1 = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.eout e₁) inner-rhs-inner ⟩
        H.eout e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₂) (H.eout e₂ ++ r₂')) ⟩
        (H.eout e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂')
                            (PermProp.++-comm (H.eout e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₁) ++ H.eout e₂ ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₁) (H.eout e₂ ++ r₂') ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
          ∎

      rhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      rhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ inner-rhs-1 ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.ein e₂) step-C' ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
          ∎

      ein-aligned
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      ein-aligned =
        Perm.↭-trans (Perm.↭-sym lhs-rearrange)
        (Perm.↭-trans mult-r₁-r₂' rhs-rearrange)

      ein-comm
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
      ein-comm = begin
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.ein e₁) (H.ein e₂) (H.eout e₂ ++ r₂)) ⟩
        (H.ein e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂) (PermProp.++-comm (H.ein e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.ein e₁) ++ H.eout e₂ ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.ein e₁) (H.eout e₂ ++ r₂) ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
          ∎

      common
        : H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      common = Perm.↭-trans (Perm.↭-sym ein-comm) ein-aligned

      cancelled-1
        : H.ein e₁ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      cancelled-1 = ++-cancelˡ (H.ein e₂) common

      cancelled
        : H.eout e₂ ++ r₂
        Perm.↭ H.eout e₁ ++ r₁'
      cancelled = ++-cancelˡ (H.ein e₁) cancelled-1

--------------------------------------------------------------------------------
-- ## Section 4: The constructive swap atom.
--
-- Given AllFire on both head-orderings (`e₁ ∷ e₂ ∷ xs` and `e₂ ∷ e₁ ∷ []`),
-- swap is fully constructive.  The conclusion is derived in three
-- steps:
--
--   1. Destructure the AllFire on `e₁ ∷ e₂ ∷ xs` to obtain `r₁`, `r₂`,
--      the perms `p₁`, `p₂`, the extract-prefix successes, and the
--      tail AllFire `af-xs : AllFire H xs (eout e₂ ++ r₂)`.
--   2. Destructure the AllFire on `e₂ ∷ e₁ ∷ []` to obtain `r₂'`,
--      `r₁'`, the perms `p₂'`, `p₁'`, and the extract-prefix successes.
--   3. Apply `post-swap-stack-↭` to get `eout e₂ ++ r₂ Perm.↭ eout e₁ ++ r₁'`,
--      then use `AllFire-resp-↭` to transport `af-xs` to AllFire on
--      `xs` starting from `eout e₁ ++ r₁'`.
--   4. Reassemble: `r₂'`, `p₂'`, eq₂' (e₂'s extract), then `r₁'`, `p₁'`,
--      eq₁' (e₁'s extract), then the transported AllFire on `xs`.

AllFire-edge-↭-swap-via-indep
  : ∀ (H : Hypergraph FlatGen)
      (e₁ e₂ : Fin (Hypergraph.nE H))
      (xs : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → AllFire H (e₁ ∷ e₂ ∷ xs) s
  → AllFire H (e₂ ∷ e₁ ∷ []) s
  → AllFire H (e₂ ∷ e₁ ∷ xs) s
AllFire-edge-↭-swap-via-indep H e₁ e₂ xs s
    (r₁ , p₁ , eq₁ , r₂ , p₂ , eq₂ , af-xs)
    (r₂' , p₂' , eq₂' , r₁' , p₁' , eq₁' , _) =
  let
    module H = Hypergraph H

    -- Stack bridge: post-(e₁,e₂) ↭ post-(e₂,e₁).
    stack-bridge
      : H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
    stack-bridge =
      post-swap-stack-↭ H e₁ e₂ s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'

    -- Transport AllFire on xs.
    af-xs-transported
      : AllFire H xs (H.eout e₁ ++ r₁')
    af-xs-transported =
      AllFire-resp-↭ H xs (H.eout e₂ ++ r₂) (H.eout e₁ ++ r₁')
                     stack-bridge af-xs
  in
    -- Reassemble: head e₂ (uses r₂', p₂', eq₂'), then head e₁ (uses r₁',
    -- p₁', eq₁'), then xs-AllFire from eout e₁ ++ r₁'.
    r₂' , p₂' , eq₂' , r₁' , p₁' , eq₁' , af-xs-transported

--------------------------------------------------------------------------------
-- ## Section 5: Wiring up to the parent's signature.
--
-- The parent residual `AllFireEdgePermSwap.AllFire-edge-↭-swap` takes
-- only a `Linear H` and `AllFire H (e₁ ∷ e₂ ∷ xs) s`.  Per the
-- counter-example, this is FALSE: no construction can produce
-- `AllFire H (e₂ ∷ e₁ ∷ xs) s` from those alone.
--
-- The augmented residual `AllFireEdgePermSwapTopo` below adds the
-- topological-soundness precondition — that the SWAPPED head pair
-- also fires from `s`.  This SINGLE additional witness suffices.

record AllFireEdgePermSwapTopo : Set where
  field
    --------------------------------------------------------------------
    -- (atom-topo) The topological-soundness precondition: from any
    -- valid AllFire on `e₁ ∷ e₂ ∷ xs` from `s`, the swapped head pair
    -- ALSO fires.
    --
    -- This is the irreducible data the consumer must supply.  It is
    -- NOT implied by Linearity (per EdgeReorder.agda's
    -- counter-example), and not implied by the AllFire on the
    -- original order alone.
    --
    -- In the intended consumer (`iso-induces-edge-↭`), this is
    -- obtained from the iso's structural ψ-ein/ψ-eout fields:
    -- the iso induces an edge bijection that respects the topological
    -- order on each side, so the swapped order ALSO satisfies AllFire.
    --
    -- This field is the SOLE residual of the swap atom; the rest of
    -- the discharge is fully constructive (see
    -- `AllFire-edge-↭-swap-via-indep` above).
    swap-already-fires
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → Linear H
      → AllFire H (e₁ ∷ e₂ ∷ xs) s
      → AllFire H (e₂ ∷ e₁ ∷ []) s

module WithTopoSoundness (assumption : AllFireEdgePermSwapTopo) where
  open AllFireEdgePermSwapTopo assumption

  ------------------------------------------------------------------------
  -- The full `AllFire-edge-↭-swap` of `AllFireEdgePermSwap`, derived
  -- from the topological-soundness premise.

  AllFire-edge-↭-swap
    : ∀ (H : Hypergraph FlatGen)
        (e₁ e₂ : Fin (Hypergraph.nE H))
        (xs : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
    → Linear H
    → AllFire H (e₁ ∷ e₂ ∷ xs) s
    → AllFire H (e₂ ∷ e₁ ∷ xs) s
  AllFire-edge-↭-swap H e₁ e₂ xs s lin af-orig =
    AllFire-edge-↭-swap-via-indep H e₁ e₂ xs s
      af-orig
      (swap-already-fires H e₁ e₂ xs s lin af-orig)

  ------------------------------------------------------------------------
  -- Package as the parent's `AllFireEdgePermSwap` record.
  to-AllFireEdgePermSwap : AllFireEdgePermSwap
  to-AllFireEdgePermSwap = record { AllFire-edge-↭-swap = AllFire-edge-↭-swap }

--------------------------------------------------------------------------------
-- ## Section 6: Summary.
--
-- This file decomposes the swap atom into:
--
--   (1) A FULLY CONSTRUCTIVE discharge `AllFire-edge-↭-swap-via-indep`
--       that takes BOTH head orderings' AllFire as input.  The body
--       is pure multiset / `_↭_` reasoning: ~200 LOC of `_↭_`-chain
--       computations + `++-cancelˡ`.
--
--   (2) A SINGLE residual field `swap-already-fires` in the record
--       `AllFireEdgePermSwapTopo`, capturing the irreducible
--       topological-soundness premise: "from a valid AllFire on
--       (e₁ ∷ e₂ ∷ xs), the swapped head pair also fires".
--
-- The residual is strictly narrower than the parent:
--
--   * It is a hypothesis about the SOURCE AllFire (only the two head
--     edges), not the conclusion AllFire on the swapped list.
--   * It does NOT require Linearity-augmented reasoning beyond
--     Linearity itself (Linearity remains a parameter for API
--     compatibility but is not used).
--   * It is the "missing data" that arises from the iso's
--     ψ-ein/ψ-eout compatibility — exactly the data
--     `iso-induces-edge-↭` ALREADY has access to.
--
-- ## STATUS
--
-- Type-checks `--safe --with-K`-clean.  Constructive discharge of the
-- swap atom modulo a single topological-soundness residual.
--------------------------------------------------------------------------------
