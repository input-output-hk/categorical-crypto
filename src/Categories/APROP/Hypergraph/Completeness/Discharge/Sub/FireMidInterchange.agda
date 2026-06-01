{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Standalone discharge of the `fire-mid-interchange` residual of
-- `Discharge/Sub/RunInterchangeEmptyTail.agda` — the both-fire two-edge
-- interchange.
--
-- ## Status of `block-nf` (the Mac-Lane block-normal-form content)
--
-- `block-nf` is now CONSTRUCTED (no longer a flat postulate): the
-- combinatorial heart of the both-fire interchange — locating BOTH input
-- blocks at once (a common residual list `Rlist` shared by the two firing
-- orders, the two block-located input permutes, the two block-located
-- OUTPUT permutes, and the output reshuffle `r-stk`) — is PROVEN
-- constructively, postulate-free, in `Sub/FireMidInterchangeComb.agda`
-- (the `SimLoc` record), using only `count`/`_↭_` algebra plus the
-- `Incomp` + `Linear` disjointness.  From that located data we build the
-- concrete `BlockNF` frames (`R`, `vin₁`, `vin₂`, `vout₁`, `vout₂`,
-- `r-stk`) as `unflatten-++-≅` re-bracketings of the locating permutes.
--
-- The SOLE remaining postulate is the four-equation residual
-- `block-nf-residual : BlockNFResidual`, packaging ONLY the categorical
-- equations over those now-PINNED frames:
--
--   * `nf₁-eq` / `nf₂-eq` — the two SINGLE-order block-normal-form
--     factorisations (one firing order's box-composite, with its blocks
--     LOCATED by the view frames, equals the 3-block tensor
--     `(box ⊗ box) ⊗ id`).  This is the genuine Mac-Lane "two boxes on
--     disjoint factors compose to a tensor of boxes" chase, of the same
--     flavour the `--with-K` development leaves open
--     (`Sub/SwapAtomAligned.swap-mac-lane-residual`).
--   * `vin-coh-eq` / `vout-coh-eq` — the σ-coherence of the two view
--     frames (the two block orders differ by the braiding on the two
--     `Aein`/`Aeout` factors).  A multi-block braiding↔`permute` bridge:
--     the same content as `FreeSMC.BraidPermute`/`BraidBlock` (both
--     `--with-K`), which provides it only at the single-atom level.
--
-- NEITHER residual field is the full `fire-mid-interchange` goal: each
-- `nfᵢ` concerns a SINGLE firing order in isolation, and the goal
-- (relating the two orders by `r-stk`) is recovered ONLY by combining
-- all four residual equations with `box-interchange` (the proven glue in
-- `fire-mid-interchange` below).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchange
  (sig : APROPSignature) where

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
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFNf2 sig as Nf2

-- The `--with-K` block-braiding ↔ `permute` machinery that the two
-- σ-coherence residual fields reduce to (previously walled off by the
-- `--without-K` co-infectivity; importable now that this module is
-- `--with-K`).  Instantiated below at `asFreeMonoidalData`.
import Categories.FreeSMC.BraidBlock
import Categories.FreeSMC.BraidPermute

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

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
  -- THE BLOCK-NORMAL-FORM RESIDUAL (M) — the genuine Mac-Lane bracketing.
  --
  -- For the two `Incomp` (disjoint-block) edges `e`, `e'`, fired in a
  -- given order from a common stack, the two framed boxes
  -- `(Agen-edge ⊗ id)` sit on disjoint tensor factors, so the composite
  -- brings to a common 3-block normal form `box-e ⊗ box-e' ⊗ id` framed by
  -- `permute`-built view isos.
  --
  -- We isolate this single bracketing residual: it provides, for the two
  -- orders, a common middle object `R` (the shared residual block) and the
  -- four `permute`-built frame morphisms, together with the factorisation
  -- of each order's box-composite into the 3-block form.  Everything else —
  -- the `box-interchange` (σ-naturality) application that swaps the two box
  -- orders and the `permute`/K reconciliation collapsing the frames into
  -- the existential reshuffle `r` — is PROVEN around it (`fire-mid-interchange`
  -- below).
  --
  -- The record's frame is stated so that the two orders share the SAME
  -- inner box-pair object `Ae ⊗₀ Ae' ⊗₀ R` / `Be ⊗₀ Be' ⊗₀ R` (where
  -- `Ae = unflatten (map vlab (ein e))` etc.), differing only in which box
  -- order (`box-e ⊗₁ box-e'` vs `box-e' ⊗₁ box-e`) sits in the middle — so
  -- `box-interchange` literally swaps them.
  ----------------------------------------------------------------------

  private
    Aein  : Fin H.nE → ObjTerm
    Aein  e = unflatten (map H.vlab (H.ein  e))
    Aeout : Fin H.nE → ObjTerm
    Aeout e = unflatten (map H.vlab (H.eout e))

    box-e : (e : Fin H.nE) → HomTerm (Aein e) (Aeout e)
    box-e e = Agen-edge H e

  -- The block-normal-form residual, per pair of disjoint edges and per the
  -- four locating permutes.  `R` is the shared residual block object.
  --
  -- The full box-composite of EACH order (`fire-mid ∘ permute ∘ fire-mid`,
  -- WITH its leading outer locating-permute folded in) factors as
  --
  --     Vout ∘ box-core ∘ Vin
  --
  -- where the two orders SHARE the same frame `(Vin , Vout)` (up to the
  -- braiding `σ` on the two box factors), `box-core` is `box-e ⊗₁ box-e'`
  -- resp. `box-e' ⊗₁ box-e` tensored with `id` on `R`, and `Vin`/`Vout`
  -- are `permute`-built isos from/to the actual stack objects.  These
  -- frames are CONSTRUCTED below from the located combinatorics; only the
  -- four categorical equations over them remain postulated (see header).
  --
  --   * `nf₁` : the `e ∷ e'` order (RHS box-composite + outer `permute p₁`).
  --   * `nf₂` : the `e' ∷ e` order (LHS box-composite + outer `permute p₂'`).
  --
  -- The frames are stated against the SAME inner object `(Aein e ⊗₀ Aein e')
  -- ⊗₀ R` (resp. out), so the two box cores are related by `box-interchange`,
  -- and the `σ`-conjugation collapses (`σ∘σ≈id`) — all PROVEN below.
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
      -- Input frame for the `e ∷ e'` order: `e`-first orientation.
      vin₁ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e ⊗₀ Aein  e') ⊗₀ R)
      -- Input frame for the `e' ∷ e` order: `e'`-first orientation.
      vin₂ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e' ⊗₀ Aein  e) ⊗₀ R)
      -- Output frames (one per final stack).
      vout₁ : HomTerm ((Aeout e ⊗₀ Aeout e') ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e' ++ r₂)))
      vout₂ : HomTerm ((Aeout e' ⊗₀ Aeout e) ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e ++ r₁')))
      -- The reshuffle between the two final stacks.
      r-stk : (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁')
      -- The two input frames differ by the braiding on the two `Aein` factors.
      vin-coh  : vin₁ ≈Term (σ ⊗₁ id) ∘ vin₂
      -- The two output frames are reconciled by `r-stk` and the braiding on
      -- the two `Aeout` factors.
      vout-coh : permute-via-vlab H.vlab r-stk ∘ vout₁ ≈Term vout₂ ∘ (σ ⊗₁ id)
      -- Block normal form of the `e ∷ e'` order (RHS, incl. outer `permute p₁`).
      nf₁  : ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term vout₁ ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id) ∘ vin₁
      -- Block normal form of the `e' ∷ e` order (LHS, incl. outer `permute p₂'`).
      nf₂  : ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term vout₂ ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id) ∘ vin₂

  ----------------------------------------------------------------------
  -- ## CONSTRUCTION of `block-nf` from the simultaneous-location
  -- combinatorics (`Comb.SimLoc`) plus a STRICTLY NARROWER residual.
  --
  -- The combinatorial heart — locating BOTH input blocks at once (a common
  -- residual `Rlist` and the two block-located input permutes), and the
  -- output reshuffle `r-stk` — is PROVEN constructively in
  -- `Sub/FireMidInterchangeComb.agda` (the `SimLoc` record), using only
  -- `count`/`_↭_` algebra + the `Incomp`/`Linear` disjointness.
  --
  -- Here we BUILD the concrete `BlockNF` frames from that located data:
  --
  --   * `R       = unflatten (map vlab Rlist)`              (the residual block)
  --   * `vin₁    = view-in₁ ∘ permute-via-vlab loc₁`        (e-first input frame)
  --   * `vin₂    = view-in₂ ∘ permute-via-vlab loc₂`        (e'-first input frame)
  --   * `vout₁   = permute-via-vlab vout-loc₁ ∘ view-out₁⁻¹`
  --   * `vout₂   = permute-via-vlab vout-loc₂ ∘ view-out₂⁻¹`
  --   * `r-stk   = SimLoc.r-stk`
  --
  -- where each `view-…` is the `unflatten-++-≅` re-bracketing of a
  -- block-located stack into `(Aein e ⊗₀ Aein e') ⊗₀ R` (resp. out), and
  -- `vout-loc₁`/`vout-loc₂` locate the two output blocks in the final
  -- stacks (`block-loc-e` applied to the *output* side).
  --
  -- The REMAINING residual `BlockNFResidual` packages ONLY the four
  -- categorical equations over these PINNED frames:
  --
  --   * `nf₁`/`nf₂` — the two single-order block-normal-form factorisations
  --     (each says: one firing order's box-composite, with its blocks now
  --     LOCATED by the view frames, IS the 3-block tensor `(box ⊗ box) ⊗ id`).
  --     This is the genuine Mac-Lane "two boxes on disjoint factors compose
  --     to a tensor of boxes" chase that even the `--with-K` development
  --     (`Sub/SwapAtomAligned.swap-mac-lane-residual`) leaves open.
  --   * `vin-coh`/`vout-coh` — the σ-coherence of the two view frames (the
  --     two block orders differ by the braiding on the two `Aein`/`Aeout`
  --     factors).  A pure `permute`-vs-`σ`-conjugate coherence over the
  --     pinned frames.
  --
  -- NEITHER residual field is the full `fire-mid-interchange` goal: each
  -- `nfᵢ` concerns a SINGLE firing order in isolation, and the goal
  -- (relating the two orders by `r-stk`) is recovered ONLY by combining
  -- `nf₁`, `nf₂`, `vin-coh`, `vout-coh`, and `box-interchange` (the proven
  -- glue in `fire-mid-interchange` below).
  ----------------------------------------------------------------------

  private
    R-obj : List (Fin H.nV) → ObjTerm
    R-obj Rlist = unflatten (map H.vlab Rlist)

    -- Map-bridged `unflatten-++-≅`: `unflatten (map vlab (As ++ Bs))`
    -- re-brackets as `unflatten (map vlab As) ⊗₀ unflatten (map vlab Bs)`.
    uf++ : (As Bs : List (Fin H.nV))
         → unflatten (map H.vlab (As ++ Bs))
           ≅ unflatten (map H.vlab As) ⊗₀ unflatten (map H.vlab Bs)
    uf++ As Bs =
      subst₂ _≅_
        (cong unflatten (sym (map-++ H.vlab As Bs)))
        refl
        (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs))

    -- The input view iso: `unflatten (map vlab ((ein a ++ ein b) ++ Rlist))`
    -- ≅ `(Aein a ⊗₀ Aein b) ⊗₀ R`.
    view-in≅
      : (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → unflatten (map H.vlab ((H.ein a ++ H.ein b) ++ Rlist))
        ≅ (Aein a ⊗₀ Aein b) ⊗₀ R-obj Rlist
    view-in≅ a b Rlist =
      ≅.trans (uf++ (H.ein a ++ H.ein b) Rlist)
              (≅⊗id (uf++ (H.ein a) (H.ein b)))
      where
        open import Categories.Morphism FreeMonoidal using (module ≅)
        -- `X ≅ Y → X ⊗₀ Z ≅ Y ⊗₀ Z` (right-whisker an iso by `id`).
        ≅⊗id : ∀ {X Y : ObjTerm} → X ≅ Y → X ⊗₀ R-obj Rlist ≅ Y ⊗₀ R-obj Rlist
        ≅⊗id i = record
          { from = _≅_.from i ⊗₁ id
          ; to   = _≅_.to   i ⊗₁ id
          ; iso  = record
            { isoˡ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                       (≈-Term-trans (⊗-resp-≈ (_≅_.isoˡ i) idˡ) id⊗id≈id)
            ; isoʳ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                       (≈-Term-trans (⊗-resp-≈ (_≅_.isoʳ i) idˡ) id⊗id≈id)
            }
          }

    -- The output view iso: identical shape on the `eout` blocks.
    view-out≅
      : (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → unflatten (map H.vlab ((H.eout a ++ H.eout b) ++ Rlist))
        ≅ (Aeout a ⊗₀ Aeout b) ⊗₀ R-obj Rlist
    view-out≅ a b Rlist =
      ≅.trans (uf++ (H.eout a ++ H.eout b) Rlist)
              (≅⊗id (uf++ (H.eout a) (H.eout b)))
      where
        open import Categories.Morphism FreeMonoidal using (module ≅)
        ≅⊗id : ∀ {X Y : ObjTerm} → X ≅ Y → X ⊗₀ R-obj Rlist ≅ Y ⊗₀ R-obj Rlist
        ≅⊗id i = record
          { from = _≅_.from i ⊗₁ id
          ; to   = _≅_.to   i ⊗₁ id
          ; iso  = record
            { isoˡ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                       (≈-Term-trans (⊗-resp-≈ (_≅_.isoˡ i) idˡ) id⊗id≈id)
            ; isoʳ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                       (≈-Term-trans (⊗-resp-≈ (_≅_.isoʳ i) idˡ) id⊗id≈id)
            }
          }

  ----------------------------------------------------------------------
  -- The CONCRETE located frames, built from `Comb.sim-loc`.  These pin
  -- the `BlockNF` existentials `R`, `vin₁`, `vin₂`, `vout₁`, `vout₂`,
  -- `r-stk` to the simultaneous-location construction.
  ----------------------------------------------------------------------

  private
    -- The located data (combinatorial heart, fully PROVEN in `Comb`).
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

  -- The residual: the four categorical equations over the PINNED frames
  -- built from `SimLoc`.  Strictly narrower than `block-nf`: the residual
  -- block `R`, all four view frames, and the reshuffle `r-stk` are no
  -- longer existential — `block-nf` below fills them with the concrete
  -- located construction; only these four equations remain.
  record BlockNFResidual : Set where
    field
      -- `nf₁`: e-first single-order block normal form (the genuine
      -- Mac-Lane "two boxes on disjoint factors = tensor of boxes" chase).
      nf₁-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
                   ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
      -- `nf₂`: e'-first single-order block normal form.
      nf₂-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                   ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
      -- `vin-coh`: the two input view frames differ by the braiding.
      vin-coh-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
             ≈Term (σ ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
      -- `vout-coh`: the two output view frames are reconciled by `r-stk`
      -- and the braiding.
      vout-coh-eq
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in permute-via-vlab H.vlab r-stk
               ∘ ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
             ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                   ∘ (σ ⊗₁ id)

  ----------------------------------------------------------------------
  -- ## Discharge of `block-nf-residual` by CONSTRUCTION (no longer a bare
  -- `postulate block-nf-residual : BlockNFResidual`).
  --
  -- The single opaque record postulate is replaced by FOUR independent,
  -- individually-typed postulates — one per `BlockNFResidual` field — each
  -- carrying EXACTLY the type of the corresponding record field.  The
  -- residual record is then BUILT from them.  This makes the trust surface
  -- explicit per categorical equation (each is separately inspectable and
  -- separately dischargeable) rather than a single opaque record, while
  -- keeping the `BlockNFResidual` record type and the `block-nf` type below
  -- BYTE-IDENTICAL so the downstream chain still wires.
  --
  -- The four equations split into two genuinely different kinds (see the
  -- module header):
  --
  --   * `nf₁-eq` / `nf₂-eq` — the genuine Mac-Lane "two boxes on disjoint
  --     factors compose to a tensor of boxes" chase on the located frames.
  --     This is the SAME flavour the dedicated `--with-K` development
  --     (`Sub/SwapAtomAligned.swap-mac-lane-residual`) ALSO leaves open —
  --     no existing module discharges it, so it stays an explicit
  --     postulate here, now isolated to its own named declaration.
  --
  --   * `vin-coh-eq` / `vout-coh-eq` — the σ-coherence of the two view
  --     frames: a multi-block braiding ↔ `permute` bridge.  The proven
  --     `--with-K` machinery for this lives in
  --     `Categories.FreeSMC.{BraidBlock,BraidPermute}` (imported below for
  --     reference / future discharge); bridging it through the concrete
  --     `unflatten-++-≅`/`subst₂`-`map-++` view-frame wrappers is the
  --     remaining Mac-Lane coherence work, isolated to its own named
  --     declaration.
  ----------------------------------------------------------------------

  -- The `--with-K` block-braiding ↔ `permute` machinery the two
  -- σ-coherence fields (`vin-coh-eq`/`vout-coh-eq`) reduce to.  Now
  -- importable because this module is `--with-K`: `σ-block` (braid one
  -- object past a nested pair) and `braid`/`braid-natural` (the iterated
  -- block braiding), plus `permute-swap-refl-σ-block` / `permute-rotate`
  -- (the atom-`permute` ↔ block-σ bridge).  Instantiated at this
  -- signature's `asFreeMonoidalData` (whose `v = Symm`, with the
  -- `Symm≤Symm` instance in scope).
  module BB = Categories.FreeSMC.BraidBlock   asFreeMonoidalData
  module BP = Categories.FreeSMC.BraidPermute asFreeMonoidalData

  -- The two σ-coherence equations of `BlockNFResidual` (the
  -- braiding ↔ `permute` bridge over the located view frames).
  postulate
    vin-coh-eq′
      : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
          (sp : List (Fin H.nV))
          (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
          (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
          (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
          (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
      → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
        in ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
           ≈Term (σ ⊗₁ id)
                 ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
    vout-coh-eq′
      : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
          (sp : List (Fin H.nV))
          (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
          (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
          (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
          (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
      → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
        in permute-via-vlab H.vlab r-stk
             ∘ ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
           ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                 ∘ (σ ⊗₁ id)

  -- The two single-order Mac-Lane block-normal-form factorisations are now
  -- DISCHARGED from a SINGLE shared residual, via `Sub/BlockNFNf2.agda`.
  -- `nf₁-eq′`/`nf₂-eq′` are MIRROR images (swap the two block roles), so both
  -- instantiate ONE symmetric generic lemma whose SOLE residual is the
  -- `BlockBracket.block-bracket` field — the shared-block two-box interchange,
  -- i.e. the genuine Mac-Lane kernel (`≈ swap-atom-aligned`, open under
  -- `--with-K` too).  This collapses the previous TWO `nf` postulates into ONE.
  postulate
    nf-bracket : Nf2.BlockBracket H
  private module NfInst = Nf2.Instantiate H nf-bracket dih lin
  nf₁-eq′ = NfInst.nf₁-eq-derived
  nf₂-eq′ = NfInst.nf₂-eq-derived

  -- The four-equation residual is now CONSTRUCTED from the four
  -- individually-typed postulates above (no bare `block-nf-residual`
  -- postulate of the opaque record).
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
    → BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
  block-nf {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' = record
    { R     = R-obj Rlist
    ; vin₁  = _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁
    ; vin₂  = _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂
    ; vout₁ = permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist)
    ; vout₂ = permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist)
    ; r-stk = r-stk
    ; vin-coh  = vin-coh-eq  inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    ; vout-coh = vout-coh-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    ; nf₁ = nf₁-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    ; nf₂ = nf₂-eq inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    }
    where
      open BlockNFResidual block-nf-residual
      open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')

  fire-mid-interchange
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    → Σ[ r ∈ (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁') ]
        ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
            ∘ fire-term H e' sp r₂' p₂' )
        ≈Term permute-via-vlab H.vlab r
                ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                      ∘ fire-term H e sp r₁ p₁ )
  fire-mid-interchange {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' =
    BlockNF.r-stk nf , goal
    where
      nf : BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
      nf = block-nf inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
      open BlockNF nf

      -- The locating permutes.
      P₁  = permute-via-vlab H.vlab p₁
      P₂  = permute-via-vlab H.vlab p₂
      P₂' = permute-via-vlab H.vlab p₂'
      P₁' = permute-via-vlab H.vlab p₁'
      Pr  = permute-via-vlab H.vlab r-stk

      bx  = box-e e
      bx' = box-e e'
      -- The (e-first) box core, the input braid `Sin` and the output braid
      -- `Sout` framing the box pair.
      C    = (bx ⊗₁ bx') ⊗₁ id {R}
      Sin  = σ {Aein  e'} {Aein  e} ⊗₁ id {R}
      Sout = σ {Aeout e} {Aeout e'} ⊗₁ id {R}

      ------------------------------------------------------------------
      -- (1)  Reassociate LHS / RHS to the `fire-mid ∘ permute ∘ …` shapes
      --      that `nf₂` / `nf₁` factor (recall `fire-term e s rest p =
      --      fire-mid e rest ∘ permute-via-vlab vlab p`, definitionally).
      ------------------------------------------------------------------
      -- LHS = (fire-mid e r₁' ∘ P₁') ∘ (fire-mid e' r₂' ∘ P₂')
      --     ≈ fire-mid e r₁' ∘ P₁' ∘ fire-mid e' r₂' ∘ P₂'   [reassoc]  = nf₂-LHS
      lhs-reassoc
        : ( fire-mid H e r₁' ∘ P₁' ) ∘ ( fire-mid H e' r₂' ∘ P₂' )
          ≈Term ( fire-mid H e r₁' ∘ P₁' ∘ fire-mid H e' r₂' ∘ P₂' )
      lhs-reassoc = assoc

      -- RHS-inner = (fire-mid e' r₂ ∘ P₂) ∘ (fire-mid e r₁ ∘ P₁)
      --           ≈ fire-mid e' r₂ ∘ P₂ ∘ fire-mid e r₁ ∘ P₁   [reassoc]  = nf₁-LHS
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

      -- (h ∘ k) ⊗₁ id ≈ (h ⊗₁ id) ∘ (k ⊗₁ id)
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
      -- (3)  Collapse the e'-first normal form to `permute r-stk ∘ nf₁-RHS`.
      --
      --   nf₂-RHS = vout₂ ∘ ((bx'⊗bx)⊗id) ∘ vin₂
      --     ≈ vout₂ ∘ (Sout ∘ (C ∘ Sin)) ∘ vin₂                 [core-swap]
      --     ≈ vout₂ ∘ Sout ∘ C ∘ (Sin ∘ vin₂)                   [assoc]
      --     ≈ vout₂ ∘ Sout ∘ C ∘ vin₁                           [≈-sym vin-coh]
      --     ≈ (vout₂ ∘ Sout) ∘ (C ∘ vin₁)                       [assoc]
      --     ≈ (permute r-stk ∘ vout₁) ∘ (C ∘ vin₁)              [≈-sym vout-coh]
      --     ≈ permute r-stk ∘ (vout₁ ∘ (C ∘ vin₁))              [assoc]
      --     = permute r-stk ∘ nf₁-RHS
      ------------------------------------------------------------------
      nf₂-RHS = vout₂ ∘ ((bx' ⊗₁ bx) ⊗₁ id) ∘ vin₂
      nf₁-RHS = vout₁ ∘ C ∘ vin₁

      collapse : nf₂-RHS ≈Term Pr ∘ nf₁-RHS
      collapse =
        -- vout₂ ∘ ((bx'⊗bx)⊗id) ∘ vin₂ ≈ vout₂ ∘ (Sout ∘ (C ∘ Sin)) ∘ vin₂
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ core-swap ≈-Term-refl))
        -- ≈ vout₂ ∘ Sout ∘ (C ∘ (Sin ∘ vin₂))
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (≈-Term-trans assoc (∘-resp-≈ ≈-Term-refl assoc)))
        -- ≈ vout₂ ∘ Sout ∘ (C ∘ vin₁)
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ ≈-Term-refl (≈-Term-sym vin-coh))))
        -- ≈ (vout₂ ∘ Sout) ∘ (C ∘ vin₁)
        (≈-Term-trans
          (≈-Term-sym assoc)
        -- ≈ (permute r-stk ∘ vout₁) ∘ (C ∘ vin₁)
        (≈-Term-trans
          (∘-resp-≈ (≈-Term-sym vout-coh) ≈-Term-refl)
        -- ≈ permute r-stk ∘ (vout₁ ∘ (C ∘ vin₁))
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
        -- LHS = (fire-mid e r₁' ∘ P₁') ∘ (fire-mid e' r₂' ∘ P₂')
        ≈-Term-trans lhs-reassoc
        -- ≈ nf₂-LHS ≈ nf₂-RHS
        (≈-Term-trans nf₂
        -- ≈ Pr ∘ nf₁-RHS
        (≈-Term-trans collapse
        -- ≈ Pr ∘ nf₁-LHS
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym nf₁))
        -- ≈ Pr ∘ ((fire-mid e' r₂ ∘ P₂) ∘ (fire-mid e r₁ ∘ P₁))   [≈-sym rhs-reassoc]
          (∘-resp-≈ ≈-Term-refl (≈-Term-sym rhs-reassoc)))))
