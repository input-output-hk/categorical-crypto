{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- A NEW, standalone discharge of the `nf₂-eq′` / `nf₁-eq′` block-normal-form
-- factorisations of `Sub/FireMidInterchange.agda` (the two postulates at
-- ~line 456/470 there).
--
-- ## What this file proves
--
-- The two postulates `nf₁-eq′` / `nf₂-eq′` are MIRROR IMAGES of each other:
-- `nf₂-eq′` is obtained from `nf₁-eq′` by the substitution
--
--   (e , e' , p₁ , p₂ , r₁ , r₂ , loc₁ , vout-loc₁)
--     ↦ (e' , e , p₂' , p₁' , r₂' , r₁' , loc₂ , vout-loc₂).
--
-- So we factor BOTH through a SINGLE generic lemma `block-nf-generic`,
-- stated over a hypergraph `H` but with the locating permutes supplied as
-- PLAIN `↭` arguments (NOT via `Comb.SimLoc`, NOT via `Incomp`).
-- `block-nf-generic` is then instantiated BOTH ways, recovering exactly the
-- types of `nf₂-eq′` (the target) and `nf₁-eq′` (the mirror).
--
-- ## Status (be honest)
--
-- The generic lemma reduces the located-firing factorisation to ONE
-- residual `BlockBracket` — the single-order "two boxes located on
-- disjoint factors = the 3-block tensor box" identity (the Mac-Lane /
-- Kelly content) — stated over the `fire-mid` boxes + the four firing /
-- locating `↭`s + the `view-in≅`/`view-out≅` re-bracketings, but STRIPPED
-- of:
--
--   * the `Comb.SimLoc` record (the locating permutes are now plain args),
--   * the `Incomp` disjointness hypothesis,
--   * the `FireMidInterchangeComb` dependency.
--
-- `BlockBracket` is symmetric in the two block orders, so the SAME residual
-- field serves BOTH `nf₁-eq′` and `nf₂-eq′`.  This is exactly the Mac-Lane
-- chase the dedicated `--with-K` development
-- (`Sub/SwapAtomAligned.swap-mac-lane-residual`) ALSO leaves open; the
-- value here is the symmetric packaging + scaffolding strip, so that ONE
-- discharge of `BlockBracket` closes both single-order normal forms.
--
-- Both `nf₂-eq-derived` (the target) and `nf₁-eq-derived` (the mirror) are
-- produced as corollaries of the single generic lemma.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFNf2
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge; Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (fire-mid)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchangeComb sig as Comb

-- The Kelly faithfulness residual `K` (over this signature's
-- `asFreeMonoidalData`).  Carried as a module parameter below: the
-- eventual proof of `block-bracket` needs it (via
-- `permute-via-vlab-≈Term-coherence-K`) to reconcile the firing locating
-- permutes against the block-locating permutes on the `Unique` codomains.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst₂)

module _ (H : Hypergraph FlatGen)
         (K : FaithfulnessResidual)
         where
  private module H = Hypergraph H

  private
    Aein  : Fin H.nE → ObjTerm
    Aein  e = unflatten (map H.vlab (H.ein  e))
    Aeout : Fin H.nE → ObjTerm
    Aeout e = unflatten (map H.vlab (H.eout e))

    box-e : (e : Fin H.nE) → HomTerm (Aein e) (Aeout e)
    box-e e = Agen-edge H e

    R-obj : List (Fin H.nV) → ObjTerm
    R-obj Rlist = unflatten (map H.vlab Rlist)

    -- Map-bridged `unflatten-++-≅`, copied from `FireMidInterchange`.
    uf++ : (As Bs : List (Fin H.nV))
         → unflatten (map H.vlab (As ++ Bs))
           ≅ unflatten (map H.vlab As) ⊗₀ unflatten (map H.vlab Bs)
    uf++ As Bs =
      subst₂ _≅_
        (cong unflatten (sym (map-++ H.vlab As Bs)))
        refl
        (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs))

    open import Categories.Morphism FreeMonoidal using (module ≅)

    ≅⊗id : ∀ {X Y : ObjTerm} (Rlist : List (Fin H.nV))
         → X ≅ Y → X ⊗₀ R-obj Rlist ≅ Y ⊗₀ R-obj Rlist
    ≅⊗id Rlist i = record
      { from = _≅_.from i ⊗₁ id
      ; to   = _≅_.to   i ⊗₁ id
      ; iso  = record
        { isoˡ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                   (≈-Term-trans (⊗-resp-≈ (_≅_.isoˡ i) idˡ) id⊗id≈id)
        ; isoʳ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                   (≈-Term-trans (⊗-resp-≈ (_≅_.isoʳ i) idˡ) id⊗id≈id)
        }
      }

    view-in≅
      : (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → unflatten (map H.vlab ((H.ein a ++ H.ein b) ++ Rlist))
        ≅ (Aein a ⊗₀ Aein b) ⊗₀ R-obj Rlist
    view-in≅ a b Rlist =
      ≅.trans (uf++ (H.ein a ++ H.ein b) Rlist)
              (≅⊗id Rlist (uf++ (H.ein a) (H.ein b)))

    view-out≅
      : (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → unflatten (map H.vlab ((H.eout a ++ H.eout b) ++ Rlist))
        ≅ (Aeout a ⊗₀ Aeout b) ⊗₀ R-obj Rlist
    view-out≅ a b Rlist =
      ≅.trans (uf++ (H.eout a ++ H.eout b) Rlist)
              (≅⊗id Rlist (uf++ (H.eout a) (H.eout b)))

  ----------------------------------------------------------------------
  -- ## The single residual (scaffolding-stripped, block-symmetric).
  --
  -- For two edges `a`, `b` fired in the order `a ∷ b` from a stack `sp`,
  -- with locating permutes
  --
  --   q-first  : sp                  ↭ ein a ++ s₁
  --   q-second : eout a ++ s₁        ↭ ein b ++ s₂
  --   loc      : sp                  ↭ (ein a ++ ein b) ++ R
  --   vout-loc : (eout a ++ eout b) ++ R ↭ eout b ++ s₂
  --
  -- the located-firing composite factors as the 3-block normal form.  This
  -- is symmetric under swapping (a,b) — so the SAME field serves the
  -- e-first and e'-first orders.
  --
  -- The residual is STRIPPED of the `Comb.SimLoc` record, the `Incomp`
  -- hypothesis, and the `FireMidInterchangeComb` dependency: the locating
  -- permutes are plain `↭` arguments.

  -- ## SOUNDNESS: the `Unique` hypotheses (`us-sp` / `us-cod`) are NOT
  -- decorative — without them the equation is FALSE-as-stated.
  --
  -- A proof must reconcile the FIRING locating permutes (`q-first` /
  -- `q-second`, inside the LHS `fire-mid ∘ permute` boxes) against the
  -- BLOCK locating permutes (`loc` / `vout-loc`, in the RHS view frames).
  -- These are independent `↭`-derivations whose codomains are
  -- re-bracketings of one another, and the ONLY device that equates
  -- `permute-via-vlab p ≈Term permute-via-vlab q` for two such derivations
  -- is the Kelly-faithfulness keystone
  -- `permute-via-vlab-≈Term-coherence-K K vlab uniq p q`, which holds ONLY
  -- when the (Fin-level) codomain `uniq` is `Unique` (the unrestricted
  -- statement is FALSE — `PermuteCoherence.Sub.PermuteCoherence`
  -- counter-example).  For a `sp` (or output stack) with a duplicated
  -- vertex one can pick `q-first` / `loc` (resp. `vout-loc`) realising
  -- DIFFERENT position bijections, and the equation fails.
  --
  --   * `us-sp  : Unique sp`              — gates the INPUT reconciliation
  --     (`q-first`/`q-second`/`loc` all have codomains that are
  --     `↭`-images of `sp`, hence `Unique` by `Unique-resp-↭`).
  --   * `us-cod : Unique (H.eout b ++ s₂)` — gates the OUTPUT reconciliation
  --     (`vout-loc`'s codomain is the FINAL stack `eout b ++ s₂`, whose
  --     freshness is the post-run reservoir fact, NOT derivable from `us-sp`).
  --
  -- These are exactly the witnesses `FireMidInterchange.block-nf` already
  -- threads (`Unique sp` + `Unique (eout e ++ r₁')`, the latter reshuffled
  -- to the other order's final stack by `r-stk`).
  record BlockBracket : Set where
    field
      block-bracket
        : ∀ (a b : Fin H.nE)
            (sp : List (Fin H.nV))
            (s₁ : List (Fin H.nV)) (q-first  : sp Perm.↭ H.ein a ++ s₁)
            (s₂ : List (Fin H.nV)) (q-second : H.eout a ++ s₁ Perm.↭ H.ein b ++ s₂)
            (R  : List (Fin H.nV))
            (loc      : sp Perm.↭ (H.ein a ++ H.ein b) ++ R)
            (vout-loc : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂)
            (us-sp  : Unique sp)
            (us-cod : Unique (H.eout b ++ s₂))
        → ( fire-mid H b s₂ ∘ permute-via-vlab H.vlab q-second
              ∘ fire-mid H a s₁ ∘ permute-via-vlab H.vlab q-first )
          ≈Term ( permute-via-vlab H.vlab vout-loc ∘ _≅_.to (view-out≅ a b R) )
                ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
                ∘ ( _≅_.from (view-in≅ a b R) ∘ permute-via-vlab H.vlab loc )

  ----------------------------------------------------------------------
  -- ## The generic block-normal-form factorisation.
  --
  -- Given the single residual, the located-firing factorisation for the
  -- order `a ∷ b` holds for arbitrary locating permutes.  This is the
  -- SYMMETRIC generic lemma: it is invariant under swapping the role of
  -- the two blocks, so it serves both `nf₁` (order `e ∷ e'`) and `nf₂`
  -- (order `e' ∷ e`).
  module _ (bb : BlockBracket) where
    open BlockBracket bb

    block-nf-generic
      : ∀ (a b : Fin H.nE)
          (sp : List (Fin H.nV))
          (s₁ : List (Fin H.nV)) (q-first  : sp Perm.↭ H.ein a ++ s₁)
          (s₂ : List (Fin H.nV)) (q-second : H.eout a ++ s₁ Perm.↭ H.ein b ++ s₂)
          (R  : List (Fin H.nV))
          (loc      : sp Perm.↭ (H.ein a ++ H.ein b) ++ R)
          (vout-loc : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂)
          (us-sp  : Unique sp)
          (us-cod : Unique (H.eout b ++ s₂))
      → ( fire-mid H b s₂ ∘ permute-via-vlab H.vlab q-second
            ∘ fire-mid H a s₁ ∘ permute-via-vlab H.vlab q-first )
        ≈Term ( permute-via-vlab H.vlab vout-loc ∘ _≅_.to (view-out≅ a b R) )
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ permute-via-vlab H.vlab loc )
    block-nf-generic = block-bracket

    ----------------------------------------------------------------------
    -- ## The two instantiations, recovering EXACTLY the `nf₂-eq′` /
    -- `nf₁-eq′` postulate types (modulo `Comb.SimLoc` being opened to
    -- supply `Rlist`, `loc₁`/`loc₂`, `vout-loc₁`/`vout-loc₂`).
    --
    -- These take the `dih`/`lin` parameters needed to BUILD `Comb.SimLoc`
    -- exactly as `FireMidInterchange` does.  They produce functions of the
    -- SAME type as the postulates `nf₂-eq′` / `nf₁-eq′`.
    module Instantiate
      (dih : ∀ {e} → ¬ (Dep H e e))
      (lin : Linear H)
      where

      open SS.PerHG H dih using (Incomp)

      private
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

      -- `nf₂-eq′`: the e'-first order (the TARGET of this task).  Blocks
      -- `a = e'`, `b = e`, `s₁ = r₂'`, `s₂ = r₁'`, `loc = loc₂`,
      -- `vout-loc = vout-loc₂`, `q-first = p₂'`, `q-second = p₁'`.
      nf₂-eq-derived
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-sp  : Unique sp) (us-cod : Unique (H.eout e ++ r₁'))
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term ( permute-via-vlab H.vlab vout-loc₂ ∘ _≅_.to (view-out≅ e' e Rlist) )
                   ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e' e Rlist) ∘ permute-via-vlab H.vlab loc₂ )
      nf₂-eq-derived {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-cod =
        block-nf-generic e' e sp r₂' p₂' r₁' p₁' Rlist loc₂ vout-loc₂ us-sp us-cod
        where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')

      -- `nf₁-eq′`: the e-first order (the MIRROR).  Blocks `a = e`,
      -- `b = e'`, `s₁ = r₁`, `s₂ = r₂`, `loc = loc₁`, `vout-loc = vout-loc₁`,
      -- `q-first = p₁`, `q-second = p₂`.
      nf₁-eq-derived
        : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
            (sp : List (Fin H.nV))
            (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
            (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
            (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
            (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
            (us-sp  : Unique sp) (us-cod : Unique (H.eout e' ++ r₂))
        → let open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
          in ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term ( permute-via-vlab H.vlab vout-loc₁ ∘ _≅_.to (view-out≅ e e' Rlist) )
                   ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id)
                   ∘ ( _≅_.from (view-in≅ e e' Rlist) ∘ permute-via-vlab H.vlab loc₁ )
      nf₁-eq-derived {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-cod =
        block-nf-generic e e' sp r₁ p₁ r₂ p₂ Rlist loc₁ vout-loc₁ us-sp us-cod
        where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
