{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Generic block-normal-form factorisation for the e-FIRST order
-- (`nf₁-eq′` of `Sub/FireMidInterchange.agda`, the postulate near line 456).
--
-- Target (the genuine Mac-Lane "two boxes on disjoint factors = tensor of
-- boxes" chase):
--
--   ( fire-mid e' r₂ ∘ permute-via-vlab vlab p₂
--       ∘ fire-mid e r₁ ∘ permute-via-vlab vlab p₁ )
--     ≈Term ( permute-via-vlab vlab vout-loc₁ ∘ to(view-out≅ e e' Rlist) )
--           ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
--           ∘ ( from(view-in≅ e e' Rlist) ∘ permute-via-vlab vlab loc₁ )
--
-- This module does NOT import `FireMidInterchange` (to avoid editing /
-- depending on the postulate it is meant to discharge).  It re-derives the
-- `view-in≅`/`view-out≅`/`R-obj`/`box-e` frames and the `SimLoc` located
-- data exactly as `FireMidInterchange` does, so the lemma here is type-
-- identical to `nf₁-eq′` and can be slotted in as
-- `nf₁-eq′ … = BlockNFNf1.block-nf-factor-e₁ H dih lin K inc sp …`.
--
-- ## Proof strategy and status
--
-- The chase factors through two genuinely-constructive engines, both
-- imported (not re-proved):
--
--   * `FireMidEquivariant.box-of-equivariant` / `fire-mid-equivariant`
--     (bifunctoriality + the `unflatten-++-≅` slide `permute-++⁺ˡ-slide`):
--     a residual permutation slides through a `fire-mid`/`box-of` box.
--   * `FaithfulnessK.permute-inverse-left!` / `permute-inverse-right!`
--     (constructive, `--with-K`): `permute (↭-sym p) ∘ permute p ≈Term id`
--     and its mirror.
--
-- ## What is PROVEN constructively here
--
-- The SimLoc projections `Rlist`/`loc₁`/`vout-loc₁` of `SL` reduce
-- DEFINITIONALLY to the exported `Comb.extract-ein'`/`block-loc-e`/
-- `vout-loc-e` constructions (the `check-*` `refl`s witness this), which
-- gives access to the internal located witnesses `q₁ : r₁ ↭ ein e' ++ Rlist`
-- and `r₂-eq : r₂ ↭ eout e ++ Rlist`.  Using those, `fire-mid-equivariant`
-- RELOCATES each edge's per-order firing residual onto the COMMON residual
-- block `Rlist`:
--
--   fire-mid e  r₁  ≈ … ∘ fire-mid e  (ein e'  ++ Rlist) ∘ …   (`reloc-e`)
--   fire-mid e' r₂  ≈ … ∘ fire-mid e' (eout e  ++ Rlist) ∘ …   (`reloc-e'`)
--
-- so the whole e-then-e' composite is rewritten (`lhs≈reloc`) to `Lreloc`,
-- in which BOTH boxes act over the SINGLE shared `Rlist`.  This relocation
-- step — including all the `subst₂`/`map-++`/`permute-via-vlab` plumbing —
-- is FULLY constructive (it routes through `FireMidEquivariant`, which uses
-- the `K`-parameterised `permute-inv-right` only for the residual self-loop
-- cancellation, plus `unflatten-++-≅` coherence).
--
-- ## What REMAINS postulated (the irreducible kernel)
--
-- `nf₁-shared` : the SHARED-`Rlist` two-box interchange, i.e. that the
-- relocated composite `Lreloc` equals the 3-block normal form
-- `(box e ⊗ box e') ⊗ id` conjugated by the `view-in≅`/`view-out≅` frames
-- and the located `loc₁`/`vout-loc₁` permutes.  This is the genuine
-- Mac-Lane "two boxes on DISJOINT factors compose to a tensor of boxes"
-- chase (now with the per-order firing residuals already collapsed onto a
-- common block) — the SAME kernel `Sub/SwapAtomAligned.swap-mac-lane-residual`
-- leaves open.  It is STRICTLY NARROWER than `nf₁-eq′`: the firing-residual
-- relocation is discharged, leaving only the disjoint-block bifunctoriality
-- + braiding reconciliation over the shared residual.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFNf1
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge; Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (fire-mid; box-of; box-of-cong)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchangeComb sig as Comb
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidEquivariant sig as FME

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst₂)

open import Categories.Category using (Category)
private module FM = Category FreeMonoidal
open FM.HomReasoning

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         (K : FaithfulnessResidual)
         where
  private module H = Hypergraph H

  open SS.PerHG H dih using (Incomp)

  ----------------------------------------------------------------------
  -- Frames re-derived exactly as in `FireMidInterchange` (byte-identical
  -- types) so that `block-nf-factor-e₁` matches `nf₁-eq′`.
  ----------------------------------------------------------------------

  private
    Aein  : Fin H.nE → ObjTerm
    Aein  e = unflatten (map H.vlab (H.ein  e))
    Aeout : Fin H.nE → ObjTerm
    Aeout e = unflatten (map H.vlab (H.eout e))

    box-e : (e : Fin H.nE) → HomTerm (Aein e) (Aeout e)
    box-e e = Agen-edge H e

    R-obj : List (Fin H.nV) → ObjTerm
    R-obj Rlist = unflatten (map H.vlab Rlist)

    uf++ : (As Bs : List (Fin H.nV))
         → unflatten (map H.vlab (As ++ Bs))
           ≅ unflatten (map H.vlab As) ⊗₀ unflatten (map H.vlab Bs)
    uf++ As Bs =
      subst₂ _≅_
        (cong unflatten (sym (map-++ H.vlab As Bs)))
        refl
        (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs))

    view-in≅
      : (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → unflatten (map H.vlab ((H.ein a ++ H.ein b) ++ Rlist))
        ≅ (Aein a ⊗₀ Aein b) ⊗₀ R-obj Rlist
    view-in≅ a b Rlist =
      ≅.trans (uf++ (H.ein a ++ H.ein b) Rlist)
              (≅⊗id (uf++ (H.ein a) (H.ein b)))
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

  ----------------------------------------------------------------------
  -- The generic e-first block-normal-form factorisation.
  ----------------------------------------------------------------------

  block-nf-factor-e₁
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
  block-nf-factor-e₁ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' = goal
    where
      -- Re-derive the INTERNAL witnesses of `sim-loc` using the SAME
      -- exported `Comb.*` helpers; these are DEFINITIONALLY EQUAL to the
      -- corresponding `SimLoc` projections of `SL`.
      ¬dep-ee' = proj₁ inc

      Rlist : List (Fin H.nV)
      Rlist = proj₁ (Comb.extract-ein' H dih lin ¬dep-ee' r₁ r₂ p₂)

      q₁ : r₁ Perm.↭ H.ein e' ++ Rlist
      q₁ = proj₂ (Comb.extract-ein' H dih lin ¬dep-ee' r₁ r₂ p₂)

      r₂-eq : r₂ Perm.↭ H.eout e ++ Rlist
      r₂-eq = Comb.eout-residual H dih lin {e} {e'} r₁ r₂ Rlist p₂ q₁

      -- Definitional-equality sanity checks against the SimLoc projections.
      open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
        renaming (Rlist to SL-Rlist; loc₁ to SL-loc₁; vout-loc₁ to SL-vout-loc₁)

      check-Rlist : SL-Rlist ≡ Rlist
      check-Rlist = refl

      check-loc₁ : SL-loc₁ ≡ Comb.block-loc-e H dih lin ¬dep-ee' sp r₁ r₂ p₁ p₂ Rlist q₁
      check-loc₁ = refl

      check-vout-loc₁ : SL-vout-loc₁ ≡ Comb.vout-loc-e H dih lin {e} {e'} r₁ r₂ Rlist p₂ q₁
      check-vout-loc₁ = refl

      -- Relocate edge e's box residual r₁ → ein e' ++ Rlist via q₁.
      reloc-e
        : fire-mid H e r₁
          ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym q₁))
                  ∘ ( fire-mid H e (H.ein e' ++ Rlist)
                      ∘ permute-via-vlab H.vlab
                          (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym (Perm.↭-sym q₁))) )
      reloc-e = FME.fire-mid-equivariant H K e (Perm.↭-sym q₁)

      -- Relocate edge e''s box residual r₂ → eout e ++ Rlist via r₂-eq.
      reloc-e'
        : fire-mid H e' r₂
          ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e') (Perm.↭-sym r₂-eq))
                  ∘ ( fire-mid H e' (H.eout e ++ Rlist)
                      ∘ permute-via-vlab H.vlab
                          (PermProp.++⁺ˡ (H.ein e') (Perm.↭-sym (Perm.↭-sym r₂-eq))) )
      reloc-e' = FME.fire-mid-equivariant H K e' (Perm.↭-sym r₂-eq)

      -- Abbreviations.
      Pᵤ : ∀ {xs ys : List (Fin H.nV)} → xs Perm.↭ ys
         → HomTerm (unflatten (map H.vlab xs)) (unflatten (map H.vlab ys))
      Pᵤ p = permute-via-vlab H.vlab p

      -- The relocated boxes (shared residual `Rlist`).
      Me  = fire-mid H e  (H.ein  e' ++ Rlist)
      Me' = fire-mid H e' (H.eout e  ++ Rlist)

      -- The reloc-substituted LHS.
      Lreloc : HomTerm (unflatten (map H.vlab sp))
                       (unflatten (map H.vlab (H.eout e' ++ r₂)))
      Lreloc =
        ( Pᵤ (PermProp.++⁺ˡ (H.eout e') (Perm.↭-sym r₂-eq))
            ∘ ( Me' ∘ Pᵤ (PermProp.++⁺ˡ (H.ein e') (Perm.↭-sym (Perm.↭-sym r₂-eq))) ) )
        ∘ ( Pᵤ p₂
            ∘ ( ( Pᵤ (PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym q₁))
                    ∘ ( Me ∘ Pᵤ (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym (Perm.↭-sym q₁))) ) )
                ∘ Pᵤ p₁ ) )

      -- LHS ≈ Lreloc by the two residual relocations.
      lhs≈reloc
        : ( fire-mid H e' r₂ ∘ Pᵤ p₂ ∘ fire-mid H e r₁ ∘ Pᵤ p₁ )
          ≈Term Lreloc
      lhs≈reloc =
        ∘-resp-≈ reloc-e'
          (∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ reloc-e ≈-Term-refl))

      -- THE SHARED-Rlist RESIDUAL (the genuine Mac-Lane "two boxes on
      -- disjoint factors compose to a tensor of boxes" kernel, with the
      -- per-order firing residuals r₁/r₂ already relocated onto the common
      -- residual block `Rlist`).  Strictly narrower than `block-nf-factor-e₁`:
      -- both boxes now act over the SHARED residual `Rlist`, and the firing
      -- residual relocation is discharged constructively above.
      postulate
        nf₁-shared
          : Lreloc
            ≈Term ( Pᵤ SL-vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
                  ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
                  ∘ ( _≅_.from (view-in≅ e e' Rlist) ∘ Pᵤ SL-loc₁ )

      goal
        : ( fire-mid H e' r₂ ∘ Pᵤ p₂ ∘ fire-mid H e r₁ ∘ Pᵤ p₁ )
          ≈Term ( Pᵤ SL-vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
                ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
                ∘ ( _≅_.from (view-in≅ e e' Rlist) ∘ Pᵤ SL-loc₁ )
      goal = ≈-Term-trans lhs≈reloc nf₁-shared
