{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharge of the `fire-mid-interchange` residual of
-- `RunInterchangeEmptyTail` — the both-fire two-edge interchange.
--
-- The combinatorial heart (a common residual `Rlist`, the two block-located
-- input/output permutes, and the reshuffle `r-stk`) is proven in
-- `Sub/FireMidInterchangeComb.agda` (`SimLoc`).  From it we build the
-- concrete `BlockNF` frames as `unflatten-++-≅` re-bracketings, and the
-- four-equation `BlockNFResidual` packages the categorical equations over
-- those pinned frames:
--   * `nf₁-eq` / `nf₂-eq` — each firing order's box-composite, with blocks
--     located, equals the 3-block tensor `(box ⊗ box) ⊗ id` (the Mac-Lane
--     chase; via `Sub/BlockNFNf2.agda`).
--   * `vin-coh-eq` / `vout-coh-eq` — σ-coherence of the two view frames
--     (the orders differ by the braiding on the `Aein`/`Aeout` factors).
--
-- Each `nfᵢ` concerns a SINGLE order; the goal (relating the two orders by
-- `r-stk`) is recovered only by combining all four with `box-interchange`
-- in `fire-mid-interchange` below.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchange
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (fire-term; fire-mid)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchangeComb sig as Comb
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFNf2 sig _≟X_ as Nf2
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance sig as SE

-- The block-braiding ↔ `permute` machinery the two σ-coherence fields
-- reduce to.
import Categories.FreeSMC.BraidBlock
import Categories.FreeSMC.BraidPermute

import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData _≟X_ as BVC

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst₂)

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open SS.PerHG H dih using (Incomp)
  open SS.FrontSwap H dih K uniq-cod using (box-interchange)

  ----------------------------------------------------------------------
  -- THE BLOCK-NORMAL-FORM record (M) — the Mac-Lane bracketing.
  --
  -- For the two `Incomp` edges fired from a common stack, the two framed
  -- boxes `(Agen-edge ⊗ id)` sit on disjoint factors, so each order's box-
  -- composite (`fire-mid ∘ permute ∘ fire-mid`, with its outer locating
  -- permute folded in) factors as `Vout ∘ box-core ∘ Vin`.  The two orders
  -- share the same inner object `(Aein e ⊗₀ Aein e') ⊗₀ R` (resp. out),
  -- differing only in the box order, so they are related by
  -- `box-interchange`.  The frames are built below from the located
  -- combinatorics; the four equations over them are discharged (see header).
  ----------------------------------------------------------------------

  -- The H-only view frames, shared with `BlockNFNf2`.
  open Nf2.ViewFrames H

  record BlockNF
    {e e' : Fin H.nE} (inc : Incomp e e')
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    : Set where
    field
      -- The shared residual block object.
      R    : ObjTerm
      -- Input frames: `e`-first / `e'`-first orientation.
      vin₁ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e ⊗₀ Aein  e') ⊗₀ R)
      vin₂ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e' ⊗₀ Aein  e) ⊗₀ R)
      -- Output frames (one per final stack).
      vout₁ : HomTerm ((Aeout e ⊗₀ Aeout e') ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e' ++ r₂)))
      vout₂ : HomTerm ((Aeout e' ⊗₀ Aeout e) ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e ++ r₁')))
      -- The reshuffle between the two final stacks.
      r-stk : (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁')
      -- The frames differ by the braiding on the two `Aein`/`Aeout` factors.
      vin-coh  : vin₁ ≈Term (σ ⊗₁ id) ∘ vin₂
      vout-coh : permute-via-vlab H.vlab r-stk ∘ vout₁ ≈Term vout₂ ∘ (σ ⊗₁ id)
      -- Block normal form of each order (incl. its outer permute).
      nf₁  : ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term vout₁ ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id) ∘ vin₁
      nf₂  : ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term vout₂ ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id) ∘ vin₂

  ----------------------------------------------------------------------
  -- The concrete located frames, built from `Comb.sim-loc`, pinning the
  -- `BlockNF` existentials.  `BlockNFResidual` then packages only the four
  -- categorical equations over these pinned frames.
  ----------------------------------------------------------------------

  private
    -- The located data (combinatorial heart, proven in `Comb`).
    SL : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
           (sp : List (Fin H.nV))
           (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
           (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
           (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
           (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
       → Comb.SimLoc H dih lin (proj₁ inc) (proj₂ inc)
                     sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' =
      Comb.sim-loc H dih lin (proj₁ inc) (proj₂ inc)
                   sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'

  -- The four categorical equations over the pinned frames from `SimLoc`.
  record BlockNFResidual : Set where
    field
      -- `nf₁`: e-first single-order block normal form (the Mac-Lane chase).
      -- The `Unique` witnesses (`us-sp`, `us-cod : Unique (eout e' ++ r₂)`
      -- — this order's final stack) feed the Kelly keystone.
      nf₁-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-sp  : Unique sp) (us-mid : Unique (H.ein e' ++ r₂))
            (us-cod : Unique (H.eout e' ++ r₂))
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
                   ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
      -- `nf₂`: e'-first single-order block normal form (mirror, with
      -- `us-cod : Unique (eout e ++ r₁')`, this order's final stack).
      nf₂-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-sp  : Unique sp) (us-mid : Unique (H.ein e ++ r₁'))
            (us-cod : Unique (H.eout e ++ r₁'))
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                   ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
      -- `vin-coh`: the input view frames differ by the braiding.  Carries
      -- `Unique sp`, used for `coh-in`'s `eval-rigid` codomain witness.
      vin-coh-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-sp : Unique sp)
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
             ≈Term (σ ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
      -- `vout-coh`: the output view frames are reconciled by `r-stk` and
      -- the braiding.  Carries `Unique (eout e ++ r₁')` for `coh-out`.
      vout-coh-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-cod : Unique (H.eout e ++ r₁'))
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in permute-via-vlab H.vlab r-stk
               ∘ ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
             ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                   ∘ (σ ⊗₁ id)

  -- The block-braiding ↔ `permute` machinery the two σ-coherence fields
  -- reduce to.
  module BB = Categories.FreeSMC.BraidBlock   asFreeMonoidalData
  module BP = Categories.FreeSMC.BraidPermute asFreeMonoidalData

  -- The two σ-coherence equations, each derived from `BlockNFVoutCoh`'s
  -- generic block-braiding consumer at the located `SimLoc` data.  The
  -- only residual is the located-permute coherence `coh-in`/`coh-out`: a
  -- vertex-level `≅↭` between the two block-located derivations into the
  -- common `Unique` codomain.
  --
  -- Each is an `eval-rigid` instance (`coh-fin-rigid` at the vertex level,
  -- lifted through `map⁺ vlab` by `map⁺-lift-≅↭`):
  --   * `coh-in` compares `loc₁` and `trans loc₂ (app-swap …)`; codomain
  --     `Unique` as the `↭`-image of `Unique sp`.
  --   * `coh-out` compares `trans vout-loc₁ r-stk` and `trans (app-swap …)
  --     vout-loc₂`; codomain is the e'-first run's final stack, whose
  --     uniqueness is a post-run freshness fact (reservoir-derived, NOT
  --     from `Unique sp` alone).
  -- Both `Unique` witnesses arrive as hypotheses `us-sp`/`us-cod` from the
  -- caller's `Linear`-backed reservoir invariant.

  coh-in
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-sp : Unique sp)
    → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      in PermProp.map⁺ H.vlab loc₁
         ≅↭ PermProp.map⁺ H.vlab
              (Perm.trans loc₂
                (BVC.app-swap H.vlab (H.ein e') (H.ein e) Rlist))
  coh-in {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp =
    SE.map⁺-lift-≅↭ H K loc₁ rhs
      (SU.coh-fin-rigid loc₁ rhs (SU.Unique-resp-↭ loc₁ us-sp))
    where
      open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      rhs = Perm.trans loc₂ (BVC.app-swap H.vlab (H.ein e') (H.ein e) Rlist)

  coh-out
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-cod : Unique (H.eout e ++ r₁'))
    → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      in PermProp.map⁺ H.vlab (Perm.trans vout-loc₁ r-stk)
         ≅↭ PermProp.map⁺ H.vlab
              (Perm.trans (BVC.app-swap H.vlab (H.eout e) (H.eout e') Rlist)
                          vout-loc₂)
  coh-out {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-cod =
    SE.map⁺-lift-≅↭ H K lhs rhs
      (SU.coh-fin-rigid lhs rhs us-cod)
    where
      open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      lhs = Perm.trans vout-loc₁ r-stk
      rhs = Perm.trans (BVC.app-swap H.vlab (H.eout e) (H.eout e') Rlist) vout-loc₂

  vin-coh-eq′
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-sp : Unique sp)
    → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      in ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
         ≈Term (σ ⊗₁ id)
               ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
  vin-coh-eq′ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp =
    BVC.vin-coh H.vlab K
      (H.ein e) (H.ein e') Rlist sp loc₁ loc₂
      (coh-in inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp)
    where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')

  vout-coh-eq′
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-cod : Unique (H.eout e ++ r₁'))
    → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      in permute-via-vlab H.vlab r-stk
           ∘ ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
         ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
               ∘ (σ ⊗₁ id)
  vout-coh-eq′ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-cod =
    BVC.vout-coh H.vlab K
      (H.eout e) (H.eout e') Rlist r₂ r₁' vout-loc₁ vout-loc₂ r-stk
      (coh-out inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-cod)
    where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')

  -- The two single-order block-normal-form factorisations are discharged
  -- from one shared residual (`BlockNFNf2.nf-bracket-proof`), reconciled
  -- by the Kelly keystone `K` — the sole trust-surface leaf of the chain.
  -- `nf₁-eq′`/`nf₂-eq′` are mirror images instantiating one generic lemma.
  nf-bracket : Nf2.BlockBracket H K
  nf-bracket = Nf2.nf-bracket-proof H K
  private module NfInst = Nf2.Instantiate H K nf-bracket dih lin
  nf₁-eq′ = NfInst.nf₁-eq-derived
  nf₂-eq′ = NfInst.nf₂-eq-derived

  block-nf-residual : BlockNFResidual
  block-nf-residual = record
    { nf₁-eq      = nf₁-eq′
    ; nf₂-eq      = nf₂-eq′
    ; vin-coh-eq  = vin-coh-eq′
    ; vout-coh-eq = vout-coh-eq′
    }

  block-nf
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-sp  : Unique sp)
        (us-mid₁ : Unique (H.eout e ++ r₁)) (us-mid₂ : Unique (H.eout e' ++ r₂'))
        (us-cod : Unique (H.eout e ++ r₁'))
    → BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
  block-nf {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid₁ us-mid₂ us-cod = record
    { R     = R-obj Rlist
    ; vin₁  = _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁
    ; vin₂  = _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂
    ; vout₁ = permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist)
    ; vout₂ = permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist)
    ; r-stk = r-stk
    ; vin-coh  = vin-coh-eq  inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp
    ; vout-coh = vout-coh-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-cod
    ; nf₁ = nf₁-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid-nf₁ us-cod₁
    ; nf₂ = nf₂-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid-nf₂ us-cod
    }
    where
      open BlockNFResidual block-nf-residual
      open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
      -- `nf₁`'s final stack `eout e' ++ r₂` is `us-cod` transported back
      -- across the reshuffle `r-stk`.
      us-cod₁ : Unique (H.eout e' ++ r₂)
      us-cod₁ = SU.Unique-resp-↭ (Perm.↭-sym r-stk) us-cod
      -- The intermediate (`q-second`-codomain) `Unique` witnesses, as
      -- `↭`-images of the per-order intermediate stacks.
      us-mid-nf₁ : Unique (H.ein e' ++ r₂)
      us-mid-nf₁ = SU.Unique-resp-↭ p₂ us-mid₁
      us-mid-nf₂ : Unique (H.ein e ++ r₁')
      us-mid-nf₂ = SU.Unique-resp-↭ p₁' us-mid₂

  fire-mid-interchange
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-sp  : Unique sp)
        (us-mid₁ : Unique (H.eout e ++ r₁)) (us-mid₂ : Unique (H.eout e' ++ r₂'))
        (us-cod : Unique (H.eout e ++ r₁'))
    → Σ[ r ∈ (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁') ]
        ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
            ∘ fire-term H e' sp r₂' p₂' )
        ≈Term permute-via-vlab H.vlab r
                ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                      ∘ fire-term H e sp r₁ p₁ )
  fire-mid-interchange {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid₁ us-mid₂ us-cod =
    BlockNF.r-stk nf , goal
    where
      nf : BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
      nf = block-nf inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid₁ us-mid₂ us-cod
      open BlockNF nf

      P₁  = permute-via-vlab H.vlab p₁
      P₂  = permute-via-vlab H.vlab p₂
      P₂' = permute-via-vlab H.vlab p₂'
      P₁' = permute-via-vlab H.vlab p₁'
      Pr  = permute-via-vlab H.vlab r-stk

      bx  = box-e e
      bx' = box-e e'
      -- The (e-first) box core and the input/output braids framing it.
      C    = (bx ⊗₁ bx') ⊗₁ id {R}
      Sin  = σ {Aein  e'} {Aein  e} ⊗₁ id {R}
      Sout = σ {Aeout e} {Aeout e'} ⊗₁ id {R}

      ------------------------------------------------------------------
      -- (1)  Reassociate LHS/RHS to the `fire-mid ∘ permute ∘ …` shapes
      --      `nf₂`/`nf₁` factor.
      ------------------------------------------------------------------
      lhs-reassoc
        : ( fire-mid H e r₁' ∘ P₁' ) ∘ ( fire-mid H e' r₂' ∘ P₂' )
          ≈Term ( fire-mid H e r₁' ∘ P₁' ∘ fire-mid H e' r₂' ∘ P₂' )
      lhs-reassoc = assoc

      rhs-reassoc
        : ( fire-mid H e' r₂ ∘ P₂ ) ∘ ( fire-mid H e r₁ ∘ P₁ )
          ≈Term ( fire-mid H e' r₂ ∘ P₂ ∘ fire-mid H e r₁ ∘ P₁ )
      rhs-reassoc = assoc

      ------------------------------------------------------------------
      -- (2)  Lift `box-interchange` through `_⊗₁ id`:
      --        (bx' ⊗₁ bx) ⊗₁ id  ≈  Sout ∘ (C ∘ Sin)
      ------------------------------------------------------------------
      bi : (bx' ⊗₁ bx) ≈Term σ ∘ ((bx ⊗₁ bx') ∘ σ)
      bi = box-interchange bx bx'

      ⊗id-∘ : ∀ {A B D} (h : HomTerm B D) (k : HomTerm A B)
            → (h ∘ k) ⊗₁ id {R} ≈Term (h ⊗₁ id) ∘ (k ⊗₁ id)
      ⊗id-∘ h k =
        ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

      core-swap : (bx' ⊗₁ bx) ⊗₁ id {R} ≈Term Sout ∘ (C ∘ Sin)
      core-swap =
        ≈-Term-trans (⊗-resp-≈ bi ≈-Term-refl)
          (≈-Term-trans (⊗id-∘ σ ((bx ⊗₁ bx') ∘ σ))
            (∘-resp-≈ ≈-Term-refl (⊗id-∘ (bx ⊗₁ bx') σ)))

      ------------------------------------------------------------------
      -- (3)  Collapse the e'-first normal form to `permute r-stk ∘ nf₁-RHS`,
      --      via `core-swap`, `vin-coh`, `vout-coh`, and re-associations.
      ------------------------------------------------------------------
      nf₂-RHS = vout₂ ∘ ((bx' ⊗₁ bx) ⊗₁ id) ∘ vin₂
      nf₁-RHS = vout₁ ∘ C ∘ vin₁

      collapse : nf₂-RHS ≈Term Pr ∘ nf₁-RHS
      collapse =
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ core-swap ≈-Term-refl))
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (≈-Term-trans assoc (∘-resp-≈ ≈-Term-refl assoc)))
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ ≈-Term-refl (≈-Term-sym vin-coh))))
        (≈-Term-trans
          (≈-Term-sym assoc)
        (≈-Term-trans
          (∘-resp-≈ (≈-Term-sym vout-coh) ≈-Term-refl)
          assoc))))

      ------------------------------------------------------------------
      -- (4)  Assemble `goal`.
      ------------------------------------------------------------------
      goal
        : ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
              ∘ fire-term H e' sp r₂' p₂' )
          ≈Term permute-via-vlab H.vlab r-stk
                  ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                        ∘ fire-term H e sp r₁ p₁ )
      goal =
        ≈-Term-trans lhs-reassoc
        (≈-Term-trans nf₂
        (≈-Term-trans collapse
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym nf₁))
          (∘-resp-≈ ≈-Term-refl (≈-Term-sym rhs-reassoc)))))
