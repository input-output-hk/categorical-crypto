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
  using (fire-mid; box-of; box-of-cong)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchangeComb sig as Comb

-- The generic, hypergraph-agnostic box / block-tensor primitives
-- (`BlockTensor.pvv-block-tensor`/`frame-ext`, `BoxAssoc.box-suffix`/
-- `box-prefix`/`box-braid`) reused as the structural template / box
-- machinery.  These are top-level submodules of `DecodeTensorShape`
-- (parameterised only by `sig` / a `vlab`), so importing them does NOT
-- pull in the `EmbedData`/`BlockFactor` decode machinery, and the cached
-- interface keeps the import cheap.  Acyclic: `DecodeTensorShape` does not
-- import this module.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig as DTS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData as BNB
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData as BNV

-- The Kelly faithfulness residual `K` (over this signature's
-- `asFreeMonoidalData`).  Carried as a module parameter below: the
-- eventual proof of `block-bracket` needs it (via
-- `permute-via-vlab-≈Term-coherence-K`) to reconcile the firing locating
-- permutes against the block-locating permutes on the `Unique` codomains.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-cong; trans-reflʳ; cong-∘)
open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

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
  -- ## Box / permute machinery for the proof of `block-bracket`.
  --
  -- `BT` is the generic block-tensor module instantiated at `H.vlab`; its
  -- `uf++` is DEFINITIONALLY the local `uf++` above (both are `BNB.uf++
  -- H.vlab`).  `pvl` is the local `permute-via-vlab H.vlab`.
  ----------------------------------------------------------------------

  private
    module FM = Category FreeMonoidal
    open FM.HomReasoning

    module BT = DTS.BlockTensor H.vlab

    pvl : {xs ys : List (Fin H.nV)} → xs Perm.↭ ys
        → HomTerm (unflatten (map H.vlab xs)) (unflatten (map H.vlab ys))
    pvl = permute-via-vlab H.vlab

    -- `BT.uf++` ≡ the local `uf++` (both `BNB.uf++ H.vlab`).
    uf++≡BT : ∀ (As Bs : List (Fin H.nV)) → uf++ As Bs ≡ BT.uf++ As Bs
    uf++≡BT As Bs = refl

    ≡⇒≈ : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
    ≡⇒≈ refl = ≈-Term-refl

    -- The keystone: two permutes with the same endpoints into a `Unique`
    -- codomain agree after `pvl`.
    pvl-coh : ∀ {zs ws : List (Fin H.nV)} → Unique ws → (p q : zs Perm.↭ ws)
            → pvl p ≈Term pvl q
    pvl-coh uniq p q = permute-via-vlab-≈Term-coherence-K K H.vlab uniq p q

    ----------------------------------------------------------------------
    -- `fire-mid` as the `uf++`-framed box `(box-e e ⊗₁ id)`.
    --
    --   fire-mid e rest ≈ to(uf++ (eout e) rest) ∘ (box-e e ⊗₁ id)
    --                       ∘ from(uf++ (ein e) rest)
    --
    -- `box-of (map vlab (ein e)) (map vlab (eout e)) (map vlab rest) (elab e)`
    -- already IS `to(raw) ∘ (box-e e ⊗₁ id) ∘ from(raw)`; the `fire-mid`
    -- `subst₂` over the `sym (map-++ …)` boundaries is exactly the
    -- `to`/`from`-subst that turns the raw `unflatten-++-≅` into `BT.uf++`
    -- (via `BNB.to-subst₂-≅`/`from-subst₂-≅`).
    fire-mid-decomp
      : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
      → fire-mid H e rest
        ≈Term _≅_.to (BT.uf++ (H.eout e) rest)
              ∘ (box-e e ⊗₁ id {R-obj rest})
              ∘ _≅_.from (BT.uf++ (H.ein e) rest)
    fire-mid-decomp e rest =
      ≈-Term-trans (≡⇒≈ step) (∘-resp-≈ (≡⇒≈ (sym to≡)) (∘-resp-≈ ≈-Term-refl (≡⇒≈ (sym from≡))))
      where
        einL  = map H.vlab (H.ein  e)
        eoutL = map H.vlab (H.eout e)
        restL = map H.vlab rest
        g     = H.elab e
        Grp   = Agen-edge-aux g                 -- = box-e e
        pIn   = cong unflatten (sym (map-++ H.vlab (H.ein  e) rest))
        pOut  = cong unflatten (sym (map-++ H.vlab (H.eout e) rest))
        rawTo   = _≅_.to   (unflatten-++-≅ eoutL restL)
        rawFrom = _≅_.from (unflatten-++-≅ einL  restL)

        -- box-of = rawTo ∘ ((Grp ⊗ id) ∘ rawFrom).  Split the `subst₂` over
        -- `∘` at the two interior objects.
        step
          : fire-mid H e rest
            ≡ subst₂ HomTerm refl pOut rawTo
              ∘ ((Grp ⊗₁ id {R-obj rest}) ∘ subst₂ HomTerm pIn refl rawFrom)
        step =
          trans (BNB.subst₂-∘-split pIn pOut rawTo
                   ((Grp ⊗₁ id {R-obj rest}) ∘ rawFrom))
                (cong (subst₂ HomTerm refl pOut rawTo ∘_)
                   (BNB.subst₂-∘-split pIn refl (Grp ⊗₁ id {R-obj rest}) rawFrom))

        to≡   : _≅_.to (BT.uf++ (H.eout e) rest) ≡ subst₂ HomTerm refl pOut rawTo
        to≡   = BNB.to-subst₂-≅ pOut (unflatten-++-≅ eoutL restL)

        from≡ : _≅_.from (BT.uf++ (H.ein e) rest) ≡ subst₂ HomTerm pIn refl rawFrom
        from≡ = BNB.from-subst₂-≅ pIn (unflatten-++-≅ einL restL)

    ----------------------------------------------------------------------
    -- ## The framed single box, and the view-frame unfoldings.
    --
    -- `Bframed e rest` = the `uf++`-framed `(box e ⊗ id)` (the RHS of
    -- `fire-mid-decomp`).
    Bframed : (e : Fin H.nE) (rest : List (Fin H.nV))
            → HomTerm (unflatten (map H.vlab (H.ein  e ++ rest)))
                      (unflatten (map H.vlab (H.eout e ++ rest)))
    Bframed e rest =
      _≅_.to (BT.uf++ (H.eout e) rest)
      ∘ (box-e e ⊗₁ id {R-obj rest})
      ∘ _≅_.from (BT.uf++ (H.ein e) rest)

    fire≈Bframed : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
                 → fire-mid H e rest ≈Term Bframed e rest
    fire≈Bframed = fire-mid-decomp

    -- The view frames `from`/`to` unfold DEFINITIONALLY into a `⊗₁ id`-whisker
    -- composed with the outer `uf++` (`≅.trans` is `from j ∘ from i` /
    -- `to i ∘ to j`, and `≅⊗id`'s `from`/`to` are `· ⊗₁ id`).
    from-view-in≡
      : ∀ (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → _≅_.from (view-in≅ a b Rlist)
        ≡ (_≅_.from (uf++ (H.ein a) (H.ein b)) ⊗₁ id {R-obj Rlist})
          ∘ _≅_.from (uf++ (H.ein a ++ H.ein b) Rlist)
    from-view-in≡ a b Rlist = refl

    to-view-out≡
      : ∀ (a b : Fin H.nE) (Rlist : List (Fin H.nV))
      → _≅_.to (view-out≅ a b Rlist)
        ≡ _≅_.to (uf++ (H.eout a ++ H.eout b) Rlist)
          ∘ (_≅_.to (uf++ (H.eout a) (H.eout b)) ⊗₁ id {R-obj Rlist})
    to-view-out≡ a b Rlist = refl

    ----------------------------------------------------------------------
    -- ## L1 — box residual-naturality (the `++⁺ˡ`-slide of a residual
    -- permute through a framed box).
    --
    --   Bframed e rest' ∘ pvl(++⁺ˡ (ein e) ρ)
    --     ≈ pvl(++⁺ˡ (eout e) ρ) ∘ Bframed e rest
    --
    -- A residual permute `ρ : rest ↭ rest'` slides through the box `box-e e`
    -- (which acts only on the front `ein e`/`eout e` block).  This is the
    -- `pvv-++⁺ˡ-slide` left-slide on BOTH frames + bifunctoriality
    -- (`box e ⊗ id` commutes with `id ⊗ pvl ρ`).  Sound (no K needed): it is
    -- pure naturality of `⊗` and the `uf++` framing.
    box-resid-slide
      : ∀ (e : Fin H.nE) {rest rest' : List (Fin H.nV)} (ρ : rest Perm.↭ rest')
      → Bframed e rest' ∘ pvl (PermProp.++⁺ˡ (H.ein e) ρ)
        ≈Term pvl (PermProp.++⁺ˡ (H.eout e) ρ) ∘ Bframed e rest
    box-resid-slide e {rest} {rest'} ρ = begin
        Bframed e rest' ∘ pvl (PermProp.++⁺ˡ (H.ein e) ρ)
          ≈⟨ refl⟩∘⟨ BT.pvv-++⁺ˡ-slide (H.ein e) ρ ⟩
        (to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ from-ei')
          ∘ (to-ei' ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei)
          ≈⟨ cancel-in ⟩
        to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eo' ∘ ((box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ)) ∘ from-ei
          ≈⟨ refl⟩∘⟨ slide-box ⟩∘⟨refl ⟩
        to-eo' ∘ ((id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest})) ∘ from-ei
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest}) ∘ from-ei
          ≈⟨ FM.sym-assoc ⟩
        (to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ)) ∘ (box-e e ⊗₁ id {R-obj rest}) ∘ from-ei
          ≈⟨ reattach-out ⟩∘⟨refl ⟩
        (pvl (PermProp.++⁺ˡ (H.eout e) ρ) ∘ to-eo) ∘ (box-e e ⊗₁ id {R-obj rest}) ∘ from-ei
          ≈⟨ FM.assoc ⟩
        pvl (PermProp.++⁺ˡ (H.eout e) ρ)
          ∘ (to-eo ∘ (box-e e ⊗₁ id {R-obj rest}) ∘ from-ei) ∎
      where
        to-ei  = _≅_.to   (uf++ (H.ein  e) rest)
        from-ei = _≅_.from (uf++ (H.ein e) rest)
        to-ei' = _≅_.to   (uf++ (H.ein  e) rest')
        from-ei' = _≅_.from (uf++ (H.ein e) rest')
        to-eo  = _≅_.to   (uf++ (H.eout e) rest)
        to-eo' = _≅_.to   (uf++ (H.eout e) rest')

        -- `from-ei' ∘ to-ei' = id` cancellation in the middle (reassoc first).
        cancel-in
          : (to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ from-ei')
              ∘ (to-ei' ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei)
            ≈Term to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei
        cancel-in = begin
          (to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ from-ei')
            ∘ (to-ei' ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei)
            ≈⟨ FM.assoc ⟩
          to-eo' ∘ ((box-e e ⊗₁ id {R-obj rest'}) ∘ from-ei')
            ∘ (to-ei' ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei)
            ≈⟨ refl⟩∘⟨ FM.assoc ⟩
          to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ from-ei'
            ∘ to-ei' ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ (from-ei' ∘ to-ei')
            ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (uf++ (H.ein e) rest') ⟩∘⟨refl ⟩
          to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ id
            ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
          to-eo' ∘ (box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ) ∘ from-ei ∎

        -- bifunctoriality: `(box e ⊗ id) ∘ (id ⊗ pvl ρ) ≈ (id ⊗ pvl ρ) ∘ (box e ⊗ id)`.
        slide-box
          : (box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ)
            ≈Term (id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest})
        slide-box = begin
          (box-e e ⊗₁ id {R-obj rest'}) ∘ (id {Aein e} ⊗₁ pvl ρ)
            ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
          (box-e e ∘ id {Aein e}) ⊗₁ (id {R-obj rest'} ∘ pvl ρ)
            ≈⟨ ⊗-resp-≈ idʳ idˡ ⟩
          box-e e ⊗₁ pvl ρ
            ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) (≈-Term-sym idʳ) ⟩
          (id {Aeout e} ∘ box-e e) ⊗₁ (pvl ρ ∘ id {R-obj rest})
            ≈⟨ ⊗-∘-dist ⟩
          (id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest}) ∎

        -- reattach the output frame: `to-eo' ∘ (id ⊗ pvl ρ) ≈ pvl(++⁺ˡ) ∘ to-eo`.
        reattach-out
          : to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ)
            ≈Term pvl (PermProp.++⁺ˡ (H.eout e) ρ) ∘ to-eo
        reattach-out = begin
          to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ)
            ≈⟨ ≈-Term-sym idʳ ⟩
          (to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ)) ∘ id
            ≈⟨ refl⟩∘⟨ ≈-Term-sym (_≅_.isoʳ (uf++ (H.eout e) rest)) ⟩
          (to-eo' ∘ (id {Aeout e} ⊗₁ pvl ρ)) ∘ (from-eo ∘ to-eo)
            ≈⟨ FM.assoc ⟩
          to-eo' ∘ ((id {Aeout e} ⊗₁ pvl ρ) ∘ (from-eo ∘ to-eo))
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          to-eo' ∘ (((id {Aeout e} ⊗₁ pvl ρ) ∘ from-eo) ∘ to-eo)
            ≈⟨ FM.sym-assoc ⟩
          (to-eo' ∘ ((id {Aeout e} ⊗₁ pvl ρ) ∘ from-eo)) ∘ to-eo
            ≈⟨ ≈-Term-sym (BT.pvv-++⁺ˡ-slide (H.eout e) ρ) ⟩∘⟨refl ⟩
          pvl (PermProp.++⁺ˡ (H.eout e) ρ) ∘ to-eo ∎
          where from-eo = _≅_.from (uf++ (H.eout e) rest)

    ----------------------------------------------------------------------
    -- ## The both-boxes-at-front morphism `Both a b`, and `Core` as `Both`
    -- framed at residual `R`.
    --
    --   Both a b = to(uf++ (eout a)(eout b)) ∘ (box a ⊗ box b)
    --                ∘ from(uf++ (ein a)(ein b))
    --     : unflatten (map vlab (ein a ++ ein b))
    --       → unflatten (map vlab (eout a ++ eout b))
    Both : (a b : Fin H.nE)
         → HomTerm (unflatten (map H.vlab (H.ein a ++ H.ein b)))
                   (unflatten (map H.vlab (H.eout a ++ H.eout b)))
    Both a b =
      _≅_.to (uf++ (H.eout a) (H.eout b))
      ∘ (box-e a ⊗₁ box-e b)
      ∘ _≅_.from (uf++ (H.ein a) (H.ein b))

    Core : (a b : Fin H.nE) (R : List (Fin H.nV))
         → HomTerm (unflatten (map H.vlab ((H.ein a ++ H.ein b) ++ R)))
                   (unflatten (map H.vlab ((H.eout a ++ H.eout b) ++ R)))
    Core a b R =
      _≅_.to (view-out≅ a b R)
      ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R})
      ∘ _≅_.from (view-in≅ a b R)

    -- `(h ∘ k ∘ l) ⊗₁ id ≈ (h ⊗₁ id) ∘ (k ⊗₁ id) ∘ (l ⊗₁ id)`.
    private
      ⊗id-∘∘ : ∀ {A B C D} {Z : ObjTerm}
                 (h : HomTerm C D) (k : HomTerm B C) (l : HomTerm A B)
             → (h ∘ k ∘ l) ⊗₁ id {Z}
               ≈Term (h ⊗₁ id {Z}) ∘ (k ⊗₁ id {Z}) ∘ (l ⊗₁ id {Z})
      ⊗id-∘∘ {Z = Z} h k l = begin
        (h ∘ k ∘ l) ⊗₁ id {Z}
          ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym (≈-Term-trans idˡ idˡ)) ⟩
        (h ∘ k ∘ l) ⊗₁ (id {Z} ∘ id {Z} ∘ id {Z})
          ≈⟨ ⊗-∘-dist ⟩
        (h ⊗₁ id {Z}) ∘ ((k ∘ l) ⊗₁ (id {Z} ∘ id {Z}))
          ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
        (h ⊗₁ id {Z}) ∘ (k ⊗₁ id {Z}) ∘ (l ⊗₁ id {Z}) ∎

    -- `Core a b R ≈ to(uf++ (eout a ++ eout b) R) ∘ (Both a b ⊗ id)
    --                ∘ from(uf++ (ein a ++ ein b) R)`.
    core≡both-framed
      : ∀ (a b : Fin H.nE) (R : List (Fin H.nV))
      → Core a b R
        ≈Term _≅_.to (uf++ (H.eout a ++ H.eout b) R)
              ∘ (Both a b ⊗₁ id {R-obj R})
              ∘ _≅_.from (uf++ (H.ein a ++ H.ein b) R)
    core≡both-framed a b R = begin
        Core a b R
          ≈⟨ ∘-resp-≈ (≡⇒≈ (to-view-out≡ a b R))
               (∘-resp-≈ ≈-Term-refl (≡⇒≈ (from-view-in≡ a b R))) ⟩
        (to-eoeo ∘ (to-eo₂ ⊗₁ id {R-obj R}))
          ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R})
          ∘ ((from-ei₂ ⊗₁ id {R-obj R}) ∘ from-eiei)
          ≈⟨ FM.assoc ⟩
        to-eoeo ∘ (to-eo₂ ⊗₁ id {R-obj R})
          ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R})
          ∘ ((from-ei₂ ⊗₁ id {R-obj R}) ∘ from-eiei)
          ≈⟨ refl⟩∘⟨ merge ⟩
        to-eoeo ∘ (Both a b ⊗₁ id {R-obj R}) ∘ from-eiei ∎
      where
        to-eoeo = _≅_.to   (uf++ (H.eout a ++ H.eout b) R)
        from-eiei = _≅_.from (uf++ (H.ein a ++ H.ein b) R)
        to-eo₂  = _≅_.to   (uf++ (H.eout a) (H.eout b))
        from-ei₂ = _≅_.from (uf++ (H.ein a) (H.ein b))

        merge
          : (to-eo₂ ⊗₁ id {R-obj R})
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R})
              ∘ ((from-ei₂ ⊗₁ id {R-obj R}) ∘ from-eiei)
            ≈Term (Both a b ⊗₁ id {R-obj R}) ∘ from-eiei
        merge = begin
          (to-eo₂ ⊗₁ id {R-obj R})
            ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R})
            ∘ ((from-ei₂ ⊗₁ id {R-obj R}) ∘ from-eiei)
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          (to-eo₂ ⊗₁ id {R-obj R})
            ∘ (((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R}) ∘ (from-ei₂ ⊗₁ id {R-obj R}))
            ∘ from-eiei
            ≈⟨ FM.sym-assoc ⟩
          ((to-eo₂ ⊗₁ id {R-obj R})
            ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id {R-obj R}) ∘ (from-ei₂ ⊗₁ id {R-obj R}))
            ∘ from-eiei
            ≈⟨ ≈-Term-sym (⊗id-∘∘ to-eo₂ (box-e a ⊗₁ box-e b) from-ei₂) ⟩∘⟨refl ⟩
          (Both a b ⊗₁ id {R-obj R}) ∘ from-eiei ∎

    ----------------------------------------------------------------------
    -- ## `both-as-fire` — `Both a b` as a sequential single-box firing.
    --
    --   Bframed b (eout a) ∘ pvl(++-comm (eout a)(ein b)) ∘ Bframed a (ein b)
    --     ≈ pvl(++-comm (eout a)(eout b)) ∘ Both a b
    --
    -- Box a fires at the front of `ein a ++ ein b` (residual `ein b`), the
    -- block-swap `++-comm (eout a)(ein b)` brings box b's input `ein b` to
    -- the front, then box b fires (residual `eout a`).  The result differs
    -- from the both-at-front `Both a b` by the OUTPUT block-swap
    -- `++-comm (eout a)(eout b)`.  No K / `Unique` needed: pure σ-naturality
    -- (`σ∘[f⊗g]≈[g⊗f]∘σ`) + bifunctoriality + the σ↔permute bridge
    -- `σ-block-comm` (proven in `BlockNFBraid`/`BlockNFVoutCoh`).
    --
    -- `BNV.σ-block-comm H.vlab` is DEFINITIONALLY at the local frames
    -- (`BNV.uf++ H.vlab = uf++`, `BNV.Aof H.vlab = Aein/Aeout`,
    -- `BNV.pvl H.vlab = pvl`).
    private
      σbc : (as bs : List (Fin H.nV))
          → _≅_.to (uf++ bs as) ∘ (σ {unflatten (map H.vlab as)} {unflatten (map H.vlab bs)})
              ∘ _≅_.from (uf++ as bs)
            ≈Term pvl (PermProp.++-comm as bs)
      σbc = BNV.σ-block-comm H.vlab

    both-as-fire
      : ∀ (a b : Fin H.nE)
      → Bframed b (H.eout a)
          ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b))
          ∘ Bframed a (H.ein b)
        ≈Term pvl (PermProp.++-comm (H.eout a) (H.eout b)) ∘ Both a b
    both-as-fire a b = begin
        Bframed b (H.eout a) ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b)) ∘ Bframed a (H.ein b)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-refl ⟩  -- `Bframed e rest` unfolds definitionally
        ( to-eobeoa ∘ box-b⊗ ∘ from-eibeoa )
          ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) )
          -- (1) pull the LEADING box-b frame out to the front (assoc twice).
          ≈⟨ FM.assoc ⟩
        to-eobeoa
          ∘ ( ( box-b⊗ ∘ from-eibeoa )
            ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) ) )
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eobeoa
          ∘ ( box-b⊗
            ∘ ( from-eibeoa
              ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) ) ) )
          -- (2) inside, expose `from-eibeoa ∘ (pvl++c ∘ to-eoaeib)` = MID', then
          --     `box-a⊗ ∘ from-eiaeib` as the tail.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ expose ⟩
        to-eobeoa
          ∘ ( box-b⊗
            ∘ ( ( from-eibeoa ∘ ( pvl++c ∘ to-eoaeib ) )
              ∘ ( box-a⊗ ∘ from-eiaeib ) ) )
          -- (3) MID' ≈ σ.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-σ ⟩∘⟨refl ⟩
        to-eobeoa
          ∘ ( box-b⊗ ∘ ( σ {Aeout a} {Aein b} ∘ ( box-a⊗ ∘ from-eiaeib ) ) )
          -- (4) regroup so `box-b⊗ ∘ σ` is a unit; apply σ-nat-b.
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eobeoa
          ∘ ( ( box-b⊗ ∘ σ {Aeout a} {Aein b} ) ∘ ( box-a⊗ ∘ from-eiaeib ) )
          ≈⟨ refl⟩∘⟨ σ-nat-b ⟩∘⟨refl ⟩
        to-eobeoa
          ∘ ( ( σ {Aeout a} {Aeout b} ∘ (id {Aeout a} ⊗₁ box-e b) )
            ∘ ( box-a⊗ ∘ from-eiaeib ) )
          -- (5) regroup so `(id ⊗ box b) ∘ box-a⊗` is a unit; apply bifun.
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eobeoa
          ∘ ( σ {Aeout a} {Aeout b}
            ∘ ( (id {Aeout a} ⊗₁ box-e b) ∘ ( box-a⊗ ∘ from-eiaeib ) ) )
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eobeoa
          ∘ ( σ {Aeout a} {Aeout b}
            ∘ ( ( (id {Aeout a} ⊗₁ box-e b) ∘ box-a⊗ ) ∘ from-eiaeib ) )
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ bifun ⟩∘⟨refl ⟩
        to-eobeoa
          ∘ ( σ {Aeout a} {Aeout b}
            ∘ ( (box-e a ⊗₁ box-e b) ∘ from-eiaeib ) )
          -- (6) regroup so `to-eobeoa ∘ σ` is a unit; apply out-σ.
          ≈⟨ FM.sym-assoc ⟩
        ( to-eobeoa ∘ σ {Aeout a} {Aeout b} )
          ∘ ( (box-e a ⊗₁ box-e b) ∘ from-eiaeib )
          ≈⟨ out-σ ⟩∘⟨refl ⟩
        ( pvl (PermProp.++-comm (H.eout a) (H.eout b)) ∘ to-eoaeob )
          ∘ ( (box-e a ⊗₁ box-e b) ∘ from-eiaeib )
          ≈⟨ FM.assoc ⟩
        pvl (PermProp.++-comm (H.eout a) (H.eout b))
          ∘ ( to-eoaeob ∘ ( (box-e a ⊗₁ box-e b) ∘ from-eiaeib ) ) ∎
      where
        box-b⊗ = box-e b ⊗₁ id {Aeout a}
        box-a⊗ = box-e a ⊗₁ id {Aein b}
        pvl++c = pvl (PermProp.++-comm (H.eout a) (H.ein b))
        to-eobeoa  = _≅_.to   (uf++ (H.eout b) (H.eout a))
        from-eibeoa = _≅_.from (uf++ (H.ein b) (H.eout a))
        to-eibeoa  = _≅_.to   (uf++ (H.ein b) (H.eout a))
        to-eoaeib  = _≅_.to   (uf++ (H.eout a) (H.ein b))
        from-eoaeib = _≅_.from (uf++ (H.eout a) (H.ein b))
        from-eiaeib = _≅_.from (uf++ (H.ein a) (H.ein b))
        to-eoaeob  = _≅_.to   (uf++ (H.eout a) (H.eout b))
        from-eoaeob = _≅_.from (uf++ (H.eout a) (H.eout b))

        -- Reassociate `from-eibeoa ∘ (pvl++c ∘ (to-eoaeib ∘ (box-a⊗ ∘ from-eiaeib))))`
        -- so that `from-eibeoa ∘ (pvl++c ∘ to-eoaeib)` (= MID') and
        -- `box-a⊗ ∘ from-eiaeib` are the two top-level units (two `sym-assoc`s).
        expose
          : from-eibeoa ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) )
            ≈Term ( from-eibeoa ∘ ( pvl++c ∘ to-eoaeib ) ) ∘ ( box-a⊗ ∘ from-eiaeib )
        expose = ≈-Term-trans (refl⟩∘⟨ FM.sym-assoc) FM.sym-assoc

        -- the middle `from(uf ei-b eo-a) ∘ pvl(++-comm eo-a ei-b) ∘ to(uf eo-a ei-b)`
        -- reduces to the bare braiding `σ {Aeout a} {Aein b}` (σ-block-comm + cancel).
        mid-σ
          : from-eibeoa ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b)) ∘ to-eoaeib
            ≈Term σ {Aeout a} {Aein b}
        mid-σ = begin
          from-eibeoa ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b)) ∘ to-eoaeib
            ≈⟨ refl⟩∘⟨ ≈-Term-sym (σbc (H.eout a) (H.ein b)) ⟩∘⟨refl ⟩
          from-eibeoa ∘ (to-eibeoa ∘ σ {Aeout a} {Aein b} ∘ from-eoaeib) ∘ to-eoaeib
            ≈⟨ refl⟩∘⟨ FM.assoc ⟩
          from-eibeoa ∘ to-eibeoa ∘ (σ {Aeout a} {Aein b} ∘ from-eoaeib) ∘ to-eoaeib
            ≈⟨ FM.sym-assoc ⟩
          (from-eibeoa ∘ to-eibeoa) ∘ (σ {Aeout a} {Aein b} ∘ from-eoaeib) ∘ to-eoaeib
            ≈⟨ _≅_.isoʳ (uf++ (H.ein b) (H.eout a)) ⟩∘⟨refl ⟩
          id ∘ (σ {Aeout a} {Aein b} ∘ from-eoaeib) ∘ to-eoaeib
            ≈⟨ idˡ ⟩
          (σ {Aeout a} {Aein b} ∘ from-eoaeib) ∘ to-eoaeib
            ≈⟨ FM.assoc ⟩
          σ {Aeout a} {Aein b} ∘ (from-eoaeib ∘ to-eoaeib)
            ≈⟨ refl⟩∘⟨ _≅_.isoʳ (uf++ (H.eout a) (H.ein b)) ⟩
          σ {Aeout a} {Aein b} ∘ id
            ≈⟨ idʳ ⟩
          σ {Aeout a} {Aein b} ∎

        -- `(box b ⊗ id) ∘ σ ≈ σ ∘ (id ⊗ box b)` (σ-naturality).
        σ-nat-b
          : (box-e b ⊗₁ id {Aeout a}) ∘ σ {Aeout a} {Aein b}
            ≈Term σ {Aeout a} {Aeout b} ∘ (id {Aeout a} ⊗₁ box-e b)
        σ-nat-b = ≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ

        -- bifunctoriality: `(id ⊗ box b) ∘ (box a ⊗ id) ≈ box a ⊗ box b`.
        bifun
          : (id {Aeout a} ⊗₁ box-e b) ∘ (box-e a ⊗₁ id {Aein b})
            ≈Term box-e a ⊗₁ box-e b
        bifun = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ idˡ idʳ)

        -- `to(uf eo-b eo-a) ∘ σ ≈ pvl(++-comm eo-a eo-b) ∘ to(uf eo-a eo-b)`.
        out-σ
          : to-eobeoa ∘ σ {Aeout a} {Aeout b}
            ≈Term pvl (PermProp.++-comm (H.eout a) (H.eout b)) ∘ to-eoaeob
        out-σ = begin
          to-eobeoa ∘ σ {Aeout a} {Aeout b}
            ≈⟨ ≈-Term-sym idʳ ⟩
          (to-eobeoa ∘ σ {Aeout a} {Aeout b}) ∘ id
            ≈⟨ refl⟩∘⟨ ≈-Term-sym (_≅_.isoʳ (uf++ (H.eout a) (H.eout b))) ⟩
          (to-eobeoa ∘ σ {Aeout a} {Aeout b}) ∘ (from-eoaeob ∘ to-eoaeob)
            ≈⟨ FM.assoc ⟩
          to-eobeoa ∘ (σ {Aeout a} {Aeout b} ∘ (from-eoaeob ∘ to-eoaeob))
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          to-eobeoa ∘ ((σ {Aeout a} {Aeout b} ∘ from-eoaeob) ∘ to-eoaeob)
            ≈⟨ FM.sym-assoc ⟩
          (to-eobeoa ∘ (σ {Aeout a} {Aeout b} ∘ from-eoaeob)) ∘ to-eoaeob
            ≈⟨ σbc (H.eout a) (H.eout b) ⟩∘⟨refl ⟩
          pvl (PermProp.++-comm (H.eout a) (H.eout b)) ∘ to-eoaeob ∎

    ----------------------------------------------------------------------
    -- ## `bframed-suffix` — the `++-assoc`-reframe lifting a framed box on
    -- a COMPOUND residual `rest ++ R` to `(Bframed e rest) ⊗ id` framed by
    -- `BT.uf++ (·++rest) R`.  This is `DTS.BoxAssoc.box-suffix` bridged
    -- across the `map H.vlab` boundary — the verbatim port of
    -- `DecodeTensorShape.box-suffix-BTC` specialised to the LOCAL `H.vlab`
    -- setting (residual `R : List (Fin H.nV)` directly, no `injR`).
    --
    -- Sound (no K): pure associativity / framing bookkeeping.
    private
      module ≡R = ≡-Reasoning

      cong₃ : ∀ {a} {A B C D : Set a} (f : A → B → C → D)
                {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z'
              → f x y z ≡ f x' y' z'
      cong₃ f refl refl refl = refl

      subst₂-HomTerm-∘
        : ∀ {A A' A'' B B' B''}
            (p₁ : A ≡ A') (p₂ : A' ≡ A'') (q₁ : B ≡ B') (q₂ : B' ≡ B'')
            (t : HomTerm A B)
        → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ t)
          ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) t
      subst₂-HomTerm-∘ refl refl refl refl t = refl

      subst₂-HomTerm-∘-dist
        : ∀ {A A' B B' C C'}
            (p : A ≡ A') (q : B ≡ B') (r : C ≡ C')
            (f : HomTerm B C) (h : HomTerm A B)
        → subst₂ HomTerm p r (f ∘ h)
          ≡ subst₂ HomTerm q r f ∘ subst₂ HomTerm p q h
      subst₂-HomTerm-∘-dist refl refl refl f h = refl

      ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
      ≡⇒≈Term refl = ≈-Term-refl

      subst₂-resp-≈Term
        : ∀ {A A' B B'} (p : A ≡ A') (q : B ≡ B') {u v : HomTerm A B}
        → u ≈Term v → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
      subst₂-resp-≈Term refl refl u≈v = u≈v

      -- to/from of `BT.uf++ As Bs` in terms of the raw `unflatten-++-≅`.
      to-BTC : ∀ (As Bs : List (Fin H.nV))
             → _≅_.to (BT.uf++ As Bs)
               ≡ subst₂ HomTerm refl (cong unflatten (sym (map-++ H.vlab As Bs)))
                   (_≅_.to (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs)))
      to-BTC As Bs = BNB.to-subst₂-≅ (cong unflatten (sym (map-++ H.vlab As Bs)))
                       (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs))

      from-BTC : ∀ (As Bs : List (Fin H.nV))
               → _≅_.from (BT.uf++ As Bs)
                 ≡ subst₂ HomTerm (cong unflatten (sym (map-++ H.vlab As Bs))) refl
                     (_≅_.from (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs)))
      from-BTC As Bs = BNB.from-subst₂-≅ (cong unflatten (sym (map-++ H.vlab As Bs)))
                         (unflatten-++-≅ (map H.vlab As) (map H.vlab Bs))

      -- `unflatten-++-≅`'s to/from under a BLOCK-1 list equality.
      to-blk1 : ∀ (Rr L L' : List X) (r : L ≡ L')
              → subst (λ z → HomTerm (unflatten z ⊗₀ unflatten Rr) (unflatten (z ++ Rr)))
                      r (_≅_.to (unflatten-++-≅ L Rr))
                ≡ _≅_.to (unflatten-++-≅ L' Rr)
      to-blk1 Rr L .L refl = refl

      from-blk1 : ∀ (Rr L L' : List X) (r : L ≡ L')
                → subst (λ z → HomTerm (unflatten (z ++ Rr)) (unflatten z ⊗₀ unflatten Rr))
                        r (_≅_.from (unflatten-++-≅ L Rr))
                  ≡ _≅_.from (unflatten-++-≅ L' Rr)
      from-blk1 Rr L .L refl = refl

      -- The combined input/output transport: the `++-assoc` plus the two
      -- `map-++ H.vlab` layers, one per box endpoint block.
      whole-eq : ∀ (lBlk rgBlk R : List (Fin H.nV))
               → map H.vlab lBlk ++ (map H.vlab rgBlk ++ map H.vlab R)
                 ≡ map H.vlab ((lBlk ++ rgBlk) ++ R)
      whole-eq lBlk rgBlk R =
        trans (sym (++-assoc (map H.vlab lBlk) (map H.vlab rgBlk) (map H.vlab R)))
        (trans (cong (_++ map H.vlab R) (sym (map-++ H.vlab lBlk rgBlk)))
               (sym (map-++ H.vlab (lBlk ++ rgBlk) R)))

    -- `box-suffix` reframed into `BT.uf++` (the `Bframed`-side middle box).
    box-suffix-BNf
      : ∀ (eiBlk eoBlk rgBlk R : List (Fin H.nV))
          (g : FlatGen (map H.vlab eiBlk) (map H.vlab eoBlk))
      → subst₂ HomTerm
          (cong unflatten (whole-eq eiBlk rgBlk R))
          (cong unflatten (whole-eq eoBlk rgBlk R))
          (box-of (map H.vlab eiBlk) (map H.vlab eoBlk)
                  (map H.vlab rgBlk ++ map H.vlab R) g)
        ≈Term _≅_.to (BT.uf++ (eoBlk ++ rgBlk) R)
              ∘ (subst₂ HomTerm
                   (cong unflatten (sym (map-++ H.vlab eiBlk rgBlk)))
                   (cong unflatten (sym (map-++ H.vlab eoBlk rgBlk)))
                   (box-of (map H.vlab eiBlk) (map H.vlab eoBlk) (map H.vlab rgBlk) g)
                   ⊗₁ id {R-obj R})
              ∘ _≅_.from (BT.uf++ (eiBlk ++ rgBlk) R)
    box-suffix-BNf eiBlk eoBlk rgBlk R g =
      ≈-Term-trans (≡⇒≈Term decomp)
        (≈-Term-trans (subst₂-resp-≈Term (cong unflatten Cei) (cong unflatten Ceo)
                         (subst₂-resp-≈Term (cong unflatten Bei) (cong unflatten Beo)
                            (DTS.BoxAssoc.box-suffix
                               (map H.vlab eiBlk) (map H.vlab eoBlk)
                               (map H.vlab rgBlk) (map H.vlab R) g)))
                      reframe)
      where
        eiL = map H.vlab eiBlk
        eoL = map H.vlab eoBlk
        rgL = map H.vlab rgBlk
        RL  = map H.vlab R

        Aei = sym (++-assoc eiL rgL RL)
        Aeo = sym (++-assoc eoL rgL RL)
        Bei = cong (_++ RL) (sym (map-++ H.vlab eiBlk rgBlk))
        Beo = cong (_++ RL) (sym (map-++ H.vlab eoBlk rgBlk))
        Cei = sym (map-++ H.vlab (eiBlk ++ rgBlk) R)
        Ceo = sym (map-++ H.vlab (eoBlk ++ rgBlk) R)

        decomp :
          subst₂ HomTerm
            (cong unflatten (whole-eq eiBlk rgBlk R))
            (cong unflatten (whole-eq eoBlk rgBlk R))
            (box-of eiL eoL (rgL ++ RL) g)
          ≡ subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
              (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                 (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
                    (box-of eiL eoL (rgL ++ RL) g)))
        decomp =
          trans
            (cong₂ (λ p q → subst₂ HomTerm p q (box-of eiL eoL (rgL ++ RL) g))
                   (cong-whole eiBlk) (cong-whole eoBlk))
            (trans
              (sym (subst₂-HomTerm-∘
                      (cong unflatten Aei) (trans (cong unflatten Bei) (cong unflatten Cei))
                      (cong unflatten Aeo) (trans (cong unflatten Beo) (cong unflatten Ceo))
                      (box-of eiL eoL (rgL ++ RL) g)))
              (sym (subst₂-HomTerm-∘
                      (cong unflatten Bei) (cong unflatten Cei)
                      (cong unflatten Beo) (cong unflatten Ceo)
                      (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
                         (box-of eiL eoL (rgL ++ RL) g)))))
          where
            cong-whole : ∀ (lBlk : List (Fin H.nV))
                       → cong unflatten (whole-eq lBlk rgBlk R)
                         ≡ trans (cong unflatten (sym (++-assoc (map H.vlab lBlk) rgL RL)))
                             (trans (cong unflatten (cong (_++ RL) (sym (map-++ H.vlab lBlk rgBlk))))
                                    (cong unflatten (sym (map-++ H.vlab (lBlk ++ rgBlk) R))))
            cong-whole lBlk =
              trans (sym (trans-cong {f = unflatten}
                            (sym (++-assoc (map H.vlab lBlk) rgL RL))))
                    (cong (trans (cong unflatten (sym (++-assoc (map H.vlab lBlk) rgL RL))))
                          (sym (trans-cong {f = unflatten}
                                  (cong (_++ RL) (sym (map-++ H.vlab lBlk rgBlk))))))

        reframe :
          subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
            (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
               (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL)
                 ∘ (box-of eiL eoL rgL g ⊗₁ id {unflatten RL})
                 ∘ _≅_.from (unflatten-++-≅ (eiL ++ rgL) RL)))
          ≈Term _≅_.to (BT.uf++ (eoBlk ++ rgBlk) R)
                ∘ (subst₂ HomTerm
                     (cong unflatten (sym (map-++ H.vlab eiBlk rgBlk)))
                     (cong unflatten (sym (map-++ H.vlab eoBlk rgBlk)))
                     (box-of eiL eoL rgL g)
                     ⊗₁ id {R-obj R})
                ∘ _≅_.from (BT.uf++ (eiBlk ++ rgBlk) R)
        reframe = ≈-Term-sym (≡⇒≈Term rhs-≡)
          where
            eirg = eiBlk ++ rgBlk
            eorg = eoBlk ++ rgBlk
            UR   = unflatten RL

            boxRg = box-of eiL eoL rgL g

            mpei = sym (map-++ H.vlab eiBlk rgBlk)
            mpeo = sym (map-++ H.vlab eoBlk rgBlk)

            ⊗-push
              : ∀ {a₁ a₂ b₁ b₂ : List X} (r₁ : a₁ ≡ a₂) (r₂ : b₁ ≡ b₂)
                  (f : HomTerm (unflatten a₁) (unflatten b₁))
              → (subst₂ HomTerm (cong unflatten r₁) (cong unflatten r₂) f) ⊗₁ id {UR}
                ≡ subst₂ HomTerm
                    (cong (λ z → unflatten z ⊗₀ UR) r₁)
                    (cong (λ z → unflatten z ⊗₀ UR) r₂)
                    (f ⊗₁ id {UR})
            ⊗-push refl refl f = refl

            subst-2 : ∀ {a b : List X} (f h : List X → ObjTerm) (r : a ≡ b)
                        (t : HomTerm (f a) (h a))
                    → subst (λ z → HomTerm (f z) (h z)) r t
                      ≡ subst₂ HomTerm (cong f r) (cong h r) t
            subst-2 f h refl t = refl

            to-eo-≡ :
              _≅_.to (BT.uf++ eorg R)
              ≡ subst₂ HomTerm
                  (trans (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl)
                  (trans (cong (λ z → unflatten (z ++ RL)) mpeo) (cong unflatten Ceo))
                  (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL))
            to-eo-≡ =
              trans (to-BTC eorg R)
              (trans (cong (subst₂ HomTerm refl (cong unflatten Ceo))
                           (trans (sym (to-blk1 RL (eoL ++ rgL) (map H.vlab eorg) mpeo))
                                  (subst-2 (λ z → unflatten z ⊗₀ UR) (λ z → unflatten (z ++ RL))
                                     mpeo
                                     (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL)))))
                     (subst₂-HomTerm-∘
                        (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl
                        (cong (λ z → unflatten (z ++ RL)) mpeo) (cong unflatten Ceo)
                        (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL))))

            from-ei-≡ :
              _≅_.from (BT.uf++ eirg R)
              ≡ subst₂ HomTerm
                  (trans (cong (λ z → unflatten (z ++ RL)) mpei) (cong unflatten Cei))
                  (trans (cong (λ z → unflatten z ⊗₀ UR) mpei) refl)
                  (_≅_.from (unflatten-++-≅ (eiL ++ rgL) RL))
            from-ei-≡ =
              trans (from-BTC eirg R)
              (trans (cong (subst₂ HomTerm (cong unflatten Cei) refl)
                           (trans (sym (from-blk1 RL (eiL ++ rgL) (map H.vlab eirg) mpei))
                                  (subst-2 (λ z → unflatten (z ++ RL)) (λ z → unflatten z ⊗₀ UR)
                                     mpei
                                     (_≅_.from (unflatten-++-≅ (eiL ++ rgL) RL)))))
                     (subst₂-HomTerm-∘
                        (cong (λ z → unflatten (z ++ RL)) mpei) (cong unflatten Cei)
                        (cong (λ z → unflatten z ⊗₀ UR) mpei) refl
                        (_≅_.from (unflatten-++-≅ (eiL ++ rgL) RL))))

            to-raw = _≅_.to   (unflatten-++-≅ (eoL ++ rgL) RL)
            fr-raw = _≅_.from (unflatten-++-≅ (eiL ++ rgL) RL)
            M      = boxRg ⊗₁ id {unflatten RL}

            Qto = trans (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl
            Qfr = trans (cong (λ z → unflatten z ⊗₀ UR) mpei) refl
            B'i = cong (λ z → unflatten (z ++ RL)) mpei
            B'o = cong (λ z → unflatten (z ++ RL)) mpeo
            P   = trans B'i (cong unflatten Cei)
            Rc  = trans B'o (cong unflatten Ceo)

            mid-≡ : (subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                      ⊗₁ id {R-obj R}
                    ≡ subst₂ HomTerm Qfr Qto M
            mid-≡ =
              trans (⊗-push mpei mpeo boxRg)
                    (cong₂ (λ p q → subst₂ HomTerm p q M)
                           (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpei)))
                           (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpeo))))

            rhs-≡ :
              _≅_.to (BT.uf++ eorg R)
                ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                     ⊗₁ id {R-obj R})
                ∘ _≅_.from (BT.uf++ eirg R)
              ≡ subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                  (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                     (to-raw ∘ M ∘ fr-raw))
            rhs-≡ = ≡R.begin
                _≅_.to (BT.uf++ eorg R)
                  ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                       ⊗₁ id {R-obj R})
                  ∘ _≅_.from (BT.uf++ eirg R)
                  ≡R.≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) to-eo-≡ mid-≡ from-ei-≡ ⟩
                subst₂ HomTerm Qto Rc to-raw
                  ∘ subst₂ HomTerm Qfr Qto M
                  ∘ subst₂ HomTerm P Qfr fr-raw
                  ≡R.≡⟨ cong (λ w → subst₂ HomTerm Qto Rc to-raw ∘ w)
                          (sym (subst₂-HomTerm-∘-dist P Qfr Qto M fr-raw)) ⟩
                subst₂ HomTerm Qto Rc to-raw
                  ∘ subst₂ HomTerm P Qto (M ∘ fr-raw)
                  ≡R.≡⟨ sym (subst₂-HomTerm-∘-dist P Qto Rc to-raw (M ∘ fr-raw)) ⟩
                subst₂ HomTerm P Rc (to-raw ∘ M ∘ fr-raw)
                  ≡R.≡⟨ sym (subst₂-HomTerm-∘
                            B'i (cong unflatten Cei)
                            B'o (cong unflatten Ceo)
                            (to-raw ∘ M ∘ fr-raw)) ⟩
                subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                  (subst₂ HomTerm B'i B'o (to-raw ∘ M ∘ fr-raw))
                  ≡R.≡⟨ cong (λ p → subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo) p)
                          (cong₂ (λ a b → subst₂ HomTerm a b (to-raw ∘ M ∘ fr-raw))
                                 (cong-∘ mpei) (cong-∘ mpeo)) ⟩
                subst₂ HomTerm (cong unflatten (Cei)) (cong unflatten Ceo)
                  (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                     (to-raw ∘ M ∘ fr-raw)) ≡R.∎

    ----------------------------------------------------------------------
    -- `bframed-suffix` — the box on a COMPOUND residual `rest ++ R`,
    -- transported across the `++-assoc` boundary, equals the box on `rest`
    -- tensored with `id` on `R`, re-framed.  The `++-assoc`/`map-++`
    -- bookkeeping collapses `box-suffix-BNf` onto `Bframed`.
    --
    -- PROVEN, postulate-free (the `box-suffix-BTC` template ported to the
    -- local `H.vlab` setting).  This is the framing primitive needed to lift
    -- `both-as-fire` to a common residual `R` for the `block-bracket`
    -- assembly.  It is a ready-to-use building block; the `block-bracket`
    -- proof that would consume it is NOT yet wired (see the `nf-bracket`
    -- postulate note in `FireMidInterchange`).
    asso : (l rest R : List (Fin H.nV))
         → map H.vlab (l ++ (rest ++ R)) ≡ map H.vlab ((l ++ rest) ++ R)
    asso l rest R = cong (map H.vlab) (sym (++-assoc l rest R))

    bframed-suffix
      : ∀ (e : Fin H.nE) (rest R : List (Fin H.nV))
      → subst₂ HomTerm
          (cong unflatten (asso (H.ein  e) rest R))
          (cong unflatten (asso (H.eout e) rest R))
          (Bframed e (rest ++ R))
        ≈Term _≅_.to (BT.uf++ (H.eout e ++ rest) R)
              ∘ (Bframed e rest ⊗₁ id {R-obj R})
              ∘ _≅_.from (BT.uf++ (H.ein e ++ rest) R)
    bframed-suffix e rest R = begin
        subst₂ HomTerm (cong unflatten (asso (H.ein e) rest R))
                       (cong unflatten (asso (H.eout e) rest R))
          (Bframed e (rest ++ R))
          ≈⟨ subst₂-resp-≈Term (cong unflatten (asso (H.ein e) rest R))
                               (cong unflatten (asso (H.eout e) rest R))
               (≈-Term-sym (fire-mid-decomp e (rest ++ R))) ⟩
        subst₂ HomTerm (cong unflatten (asso (H.ein e) rest R))
                       (cong unflatten (asso (H.eout e) rest R))
          (fire-mid H e (rest ++ R))
          -- `fire-mid e (rest++R) = subst₂ Pin Pout (box-of … (map vlab (rest++R)) …)`;
          -- collapse the stacked substs to a single subst over `box-of (rest++R)`,
          -- then UIP-collapse onto box-suffix-BNf's LHS subst.
          ≈⟨ ≡⇒≈Term collapse ⟩
        subst₂ HomTerm
          (cong unflatten (whole-eq (H.ein e) rest R))
          (cong unflatten (whole-eq (H.eout e) rest R))
          (box-of einL eoutL (map H.vlab rest ++ map H.vlab R) g)
          ≈⟨ box-suffix-BNf (H.ein e) (H.eout e) rest R g ⟩
        _≅_.to (BT.uf++ (H.eout e ++ rest) R)
          ∘ (FireRest ⊗₁ id {R-obj R})
          ∘ _≅_.from (BT.uf++ (H.ein e ++ rest) R)
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (fire-mid-decomp e rest) ≈-Term-refl ⟩∘⟨refl ⟩
        _≅_.to (BT.uf++ (H.eout e ++ rest) R)
          ∘ (Bframed e rest ⊗₁ id {R-obj R})
          ∘ _≅_.from (BT.uf++ (H.ein e ++ rest) R) ∎
      where
        einL  = map H.vlab (H.ein  e)
        eoutL = map H.vlab (H.eout e)
        g     = H.elab e

        Pin  = cong unflatten (sym (map-++ H.vlab (H.ein  e) (rest ++ R)))
        Pout = cong unflatten (sym (map-++ H.vlab (H.eout e) (rest ++ R)))

        -- The `box-of-cong` residual reconciliation
        -- `map vlab (rest++R) ≡ map vlab rest ++ map vlab R`.
        Fin' : einL ++ map H.vlab (rest ++ R) ≡ einL ++ (map H.vlab rest ++ map H.vlab R)
        Fin' = cong₂ _++_ refl (map-++ H.vlab rest R)
        Fout : eoutL ++ map H.vlab (rest ++ R) ≡ eoutL ++ (map H.vlab rest ++ map H.vlab R)
        Fout = cong₂ _++_ refl (map-++ H.vlab rest R)

        FireRest : HomTerm (unflatten (map H.vlab (H.ein e ++ rest)))
                           (unflatten (map H.vlab (H.eout e ++ rest)))
        FireRest = subst₂ HomTerm
                     (cong unflatten (sym (map-++ H.vlab (H.ein  e) rest)))
                     (cong unflatten (sym (map-++ H.vlab (H.eout e) rest)))
                     (box-of einL eoutL (map H.vlab rest) g)

        bc : box-of einL eoutL (map H.vlab rest ++ map H.vlab R) g
             ≡ subst₂ HomTerm (cong unflatten Fin') (cong unflatten Fout)
                 (box-of einL eoutL (map H.vlab (rest ++ R)) g)
        bc = sym (box-of-cong {restL₁ = map H.vlab (rest ++ R)}
                              {restL₂ = map H.vlab rest ++ map H.vlab R}
                    refl refl (map-++ H.vlab rest R) g g refl)

        collapse :
          subst₂ HomTerm (cong unflatten (asso (H.ein e) rest R))
                         (cong unflatten (asso (H.eout e) rest R))
            (fire-mid H e (rest ++ R))
          ≡ subst₂ HomTerm
              (cong unflatten (whole-eq (H.ein e) rest R))
              (cong unflatten (whole-eq (H.eout e) rest R))
              (box-of einL eoutL (map H.vlab rest ++ map H.vlab R) g)
        collapse =
          trans (subst₂-HomTerm-∘ Pin (cong unflatten (asso (H.ein e) rest R))
                                  Pout (cong unflatten (asso (H.eout e) rest R))
                                  (box-of einL eoutL (map H.vlab (rest ++ R)) g))
          (trans
            (cong₂ (λ p q → subst₂ HomTerm p q (box-of einL eoutL (map H.vlab (rest ++ R)) g))
                   (uip (trans Pin (cong unflatten (asso (H.ein e) rest R)))
                        (trans (cong unflatten Fin') (cong unflatten (whole-eq (H.ein e) rest R))))
                   (uip (trans Pout (cong unflatten (asso (H.eout e) rest R)))
                        (trans (cong unflatten Fout) (cong unflatten (whole-eq (H.eout e) rest R)))))
            (trans
              (sym (subst₂-HomTerm-∘
                      (cong unflatten Fin') (cong unflatten (whole-eq (H.ein e) rest R))
                      (cong unflatten Fout) (cong unflatten (whole-eq (H.eout e) rest R))
                      (box-of einL eoutL (map H.vlab (rest ++ R)) g)))
              (cong (subst₂ HomTerm (cong unflatten (whole-eq (H.ein e) rest R))
                                    (cong unflatten (whole-eq (H.eout e) rest R)))
                    (sym bc))))

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
