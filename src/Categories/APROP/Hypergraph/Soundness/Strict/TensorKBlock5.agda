{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 6: discharge `HeadProviderˢ` (the GATE) and instantiate `kfac-genˢ` →
-- `KBlockσ` → the UNCONDITIONAL strict ⊗-shape `decodePˢ-⊗`.
--
-- The per-edge HEAD reconciliation (`HeadReconcileˢ`) is discharged from two
-- proven strict bricks:
--   * `StackEquivS.edge-step-equivariantˢ` — conjugate the ACTUAL fired head
--     `tH` on the actual stack `s` onto the CLEAN stack `L ++ s_R` via `pf`.
--   * `TKB3.fire-slideˢ` — on the clean stack the K-edge fires past the carried
--     `L`-block (disjoint from K's `ein = map injR (K.ein eK)`), giving the
--     `idˢ {m L} ⊗ˢ fire` framed head `KCleanHeadˢ` up to the output braid.
--
-- The equivariance step uses `pvv-transˢ` (DEFINITIONAL `permuteˢ ∘`-split) so
-- the conjugation glue is pure `≈ˢ`-algebra; the genuine content is the clean
-- per-edge SLIDE (`HeadSlideˢ`), discharged separately by the FIRE/SKIP
-- dispatch built on `fire-slideˢ` + the `↑ʳ`-disjointness.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock5
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.StackEquivS sig _≟X_
  using (module EquivStep)
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock4 sig _≟X_ as TKB4

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
  open EquivStep H using ( pvv-transˢ; pvv-inverse-leftˢ; pvv-inverse-rightˢ
                         ; edge-stepˢ-graph; edge-step-equivariantˢ )

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  module _ (permˢ-K : Kmod.PermK) where
    KCleanHeadˢ = TKB4.KCleanHeadˢ H permˢ-K
    HeadReconcileˢ = TKB4.HeadReconcileˢ H permˢ-K
    HeadProviderˢ = TKB4.HeadProviderˢ H permˢ-K

    ----------------------------------------------------------------------
    -- ## The clean per-edge SLIDE interface.
    --
    -- For a head edge `e` whose inputs are disjoint from the carried block
    -- `L`, fired on the CLEAN stack `L ++ s_R`, there is a braid `β` from the
    -- clean post-edge stack to `L ++ (edge-stepˢ s_R e).₁` such that the clean
    -- fired head, braided by `β`, IS the framed clean head `KCleanHeadˢ`.
    --
    -- This is the genuine per-edge content (`fire-slideˢ` + the `↑ʳ`-disjoint
    -- skip/fire dispatch); the equivariance conjugation below is built on it.
    ----------------------------------------------------------------------

    HeadSlideˢ : (e : Fin H.nE) (L s_R : List (Fin H.nV)) → Set
    HeadSlideˢ e L s_R =
      Σ[ β ∈ (proj₁ (edge-stepˢ (L ++ s_R) e))
               Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
        ( permuteˢ β ∘ˢ proj₂ (edge-stepˢ (L ++ s_R) e)
          ≈ˢ KCleanHeadˢ e L s_R )

    ----------------------------------------------------------------------
    -- ## The equivariance conjugation glue.
    --
    -- Given `HeadSlideˢ` and the post-edge `Unique`, `HeadReconcileˢ` follows
    -- by conjugating the actual fired head onto the clean stack via
    -- `edge-step-equivariantˢ` and reassociating.
    ----------------------------------------------------------------------

    head-reconcile-from-slide
      : ∀ (e : Fin H.nE) (L s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → HeadSlideˢ e L s_R
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
            pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e))
    head-reconcile-from-slide e L s_R s pf us (β , slide)
      with edge-step-equivariantˢ e pf
             (edge-stepˢ-graph (L ++ s_R) e) (edge-stepˢ-graph s e) us
    ... | ρf , eq =
      Perm.trans ρf β , goal
      where
        tH      = proj₂ (edge-stepˢ s e)
        tHclean = proj₂ (edge-stepˢ (L ++ s_R) e)

        -- eq : tH ≈ permuteˢ (↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)
        -- goal : permuteˢ (trans ρf β) ∘ tH ≈ KCleanHeadˢ ∘ permuteˢ pf
        goal
          : permuteˢ (Perm.trans ρf β) ∘ˢ tH
            ≈ˢ KCleanHeadˢ e L s_R ∘ˢ permuteˢ pf
        goal =
          -- permuteˢ (trans ρf β) = permuteˢ β ∘ permuteˢ ρf  (definitional)
          ≈-trans (∘-resp (pvv-transˢ ρf β) ≈-refl)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ tH
          (≈-trans (∘-resp ≈-refl eq)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans assocˢ
          -- permuteˢ β ∘ (permuteˢ ρf ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)))
          (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          -- permuteˢ β ∘ ((permuteˢ ρf ∘ permuteˢ(↭-sym ρf)) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl (∘-resp (pvv-inverse-rightˢ ρf) ≈-refl))
          -- permuteˢ β ∘ (idˢ ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl idˡ)
          -- permuteˢ β ∘ (tHclean ∘ permuteˢ pf)
          (≈-trans (≈-sym assocˢ)
          -- (permuteˢ β ∘ tHclean) ∘ permuteˢ pf
          (∘-resp slide ≈-refl)))))))

--------------------------------------------------------------------------------
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to `KBlockσ`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--
--   * `HeadSlideˢ` — the per-edge CLEAN-SLIDE interface: for a head edge `e`
--     fired on the clean stack `L ++ s_R`, a braid `β` such that the clean
--     fired head braided by `β` IS the framed clean head `KCleanHeadˢ`.  This
--     is the `fire-slideˢ` + `↑ʳ`-disjoint content, ABSTRACTED so the
--     equivariance conjugation is independent of the concrete layout.
--
--   * `head-reconcile-from-slide` — THE GATE REDUCTION.  Discharges the per-edge
--     `HeadReconcileˢ` of `TKB4` from `HeadSlideˢ`, by conjugating the actual
--     fired head `tH` onto the clean stack `L ++ s_R` via
--     `StackEquivS.edge-step-equivariantˢ` (at `ρ = pf`) and reassociating.
--     The advanced clean perm is `pf1 = trans ρf β` (the equivariance braid
--     `ρf` chained with the slide braid `β`); `permuteˢ` splits over `trans`
--     DEFINITIONALLY (`pvv-transˢ`), and the round-trip `permuteˢ ρf ∘
--     permuteˢ (↭-sym ρf)` collapses by `pvv-inverse-rightˢ`.  UNCONDITIONAL
--     against `HeadSlideˢ`.
--
-- The equivariance conjugation (c′-glue) is therefore COMPLETE and generic; the
-- gate is reduced to the two uniform families.
--
-- REMAINING (the genuine concrete content + the assembly tail):
--
--   (c′-slide) DISCHARGE `HeadSlideˢ` at the `hTensor` layout: `H = ⟪f⊗₁g⟫`,
--        `L = map injL Gd.dom`, `s_R = map injR ys`, `e = ψK eK = Gd.nE ↑ʳ eK`.
--        FIRE case: `edge-stepˢ (L ++ s_R) (ψK eK)` reduces (strict twin of
--        `extract-prefix-↑ʳ-on-mixed-just`, needed) to
--          `fire-termˢ (ψK eK) (L ++ s_R) (L ++ map injR rest) q`,
--        whose residual is LITERALLY `L ++ (edge-stepˢ s_R (ψK eK)).₁` because
--        K's `ein = map injR (K.ein eK)` is disjoint from `L = map injL …`.
--        This is exactly `fire-slideˢ`'s LHS at `xs = s_R`, `rest = map injR
--        rest`; `fire-slideˢ` rewrites it to `castₒ(permuteˢ (obraid)) ∘
--        (idˢ{m L} ⊗ˢ fire-termˢ … s_R …)`, and the framed `idˢ{m L} ⊗ˢ …`
--        factor IS `KCleanHeadˢ` (definitional).  The slide braid `β` is read
--        off `obraid` (the output block-braid sliding K's eout back past `L`),
--        absorbed via the cast algebra into the `HeadSlideˢ` Σ.  SKIP case:
--        both `edge-stepˢ` reduce to `idˢ` (via the strict twin of
--        `extract-prefix-↑ʳ-on-mixed-nothing`), and `KCleanHeadˢ` collapses by
--        `⊗-id`/`cast-id`; `β = ↭-refl`.  Estimated ~250-350 LOC; the only NEW
--        substrate is the strict twin of the term-FREE `edge-step-↑ʳ-on-mixed-
--        {just,nothing}` stack reductions (the non-strict ones live in
--        `Soundness/DecodeAttempt`); they transfer because the strict and
--        non-strict runs walk the SAME stacks (`Run.stacks-agree`).  The
--        `Unique`-advance family is the strict-run reservoir freshness from
--        `Discharge/Sub/StackUniqueReach` (as in `process-edges-equivariantˢ`).
--
--   (d) INSTANTIATE `kfac-genˢ` at `TensorBraidS.Braid.Krun` (the K-block run on
--        the actual post-G stack `proj₁ (process-edgesˢ gblk Hf.dom)`), with
--        `L = Lpre`, `s_R = Rsuf`, `pf` the `gframe`/`stack-sepˢ` clean perm,
--        and `Br` the accumulated K-prepend braid; relabel the clean K-run to
--        `decodePˢ g` via `Kon-bridge` + `DecodeComposeS.permuteˢ-X`.
--
--   (e) RECONCILE with `gframe`/`Gon-bridge` (G-side = `decodePˢ f`), collapse
--        the accumulated `Br` braid + `permuteˢ cand` (final extract-exact
--        permute) by `perm-rigidˢ` on `Unique Hf.cod` → the `KBlockσ` witness;
--        feed to `TensorBraidS.Braid.decodePˢ-⊗-cond` → the UNCONDITIONAL
--        `decodePˢ-⊗`.
--
-- STATUS: the per-edge GATE (`HeadReconcileˢ` ⇐ `HeadSlideˢ`) and its packaging
-- into `HeadProviderˢ` are PROVEN and generic; the K-block fold `kfac-genˢ`
-- (TKB4) consumes the result UNCONDITIONALLY.  `decodePˢ-⊗` is NOT YET
-- unconditional: it still rests on (c′-slide) [the concrete strict
-- `edge-step-↑ʳ-on-mixed` term reductions + `fire-slideˢ` alignment] and the
-- (d)/(e) reconcile to `KBlockσ`.  NO postulate is introduced.
--------------------------------------------------------------------------------
