{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `nf₂-eq′` / `nf₁-eq′` block-normal-form factorisations used by
-- `Sub/FireMidInterchange.agda`.
--
-- The two factorisations are MIRROR IMAGES of each other, so we factor BOTH
-- through a SINGLE generic lemma `block-nf-generic`, stated over a
-- hypergraph `H` with the locating permutes supplied as PLAIN `↭` arguments
-- (NOT via `Comb.SimLoc`, NOT via `Incomp`).  `block-nf-generic` is then
-- instantiated BOTH ways, recovering the types of `nf₂-eq′` and `nf₁-eq′`.
--
-- The generic lemma reduces the located-firing factorisation to ONE
-- residual `BlockBracket` — the single-order "two boxes located on disjoint
-- factors = the 3-block tensor box" identity (the Mac-Lane / Kelly
-- content).  `BlockBracket` is symmetric in the two block orders, so ONE
-- discharge (`nf-bracket-proof`) closes both single-order normal forms.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFNf2
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

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

-- The hypergraph-agnostic box / block-tensor primitives, reused as the box
-- machinery.  Top-level submodules of `DecodeTensorShape` (parameterised
-- only by `sig` / a `vlab`), so importing them does NOT pull in the decode
-- machinery.  Acyclic: `DecodeTensorShape` does not import this module.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig _≟X_ as DTS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData _≟X_ as BNB
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData _≟X_ as BNV

-- The Kelly faithfulness residual `K`.  The proof of `block-bracket` needs
-- it (via `permute-via-vlab-≈Term-coherence-K`) to reconcile the firing
-- locating permutes against the block-locating permutes on `Unique` codomains.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
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

-- Hedberg UIP on `ObjTerm` from decidable equality on `X` (replaces the
-- `--with-K` `uip`, illegal under `--without-K`).
open import Categories.APROP.Hypergraph.Completeness.Discharge.ObjUIP
  using (module ObjUIP)

uip : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
uip = ObjUIP.objUIP′ {Symm} {X} _≟X_

-- The H-only (K-FREE) "view frames": the `Aein`/`Aeout`/`box-e`/`R-obj`/
-- `uf++`/`≅⊗id`/`view-in≅`/`view-out≅` block re-bracketings.  PUBLIC so
-- `Sub/FireMidInterchange.agda` can share it verbatim.  The `uf++` here is
-- DEFINITIONALLY `BNB.uf++ H.vlab` (= `BT.uf++`).
module ViewFrames (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  Aein  : Fin H.nE → ObjTerm
  Aein  e = unflatten (map H.vlab (H.ein  e))
  Aeout : Fin H.nE → ObjTerm
  Aeout e = unflatten (map H.vlab (H.eout e))

  box-e : (e : Fin H.nE) → HomTerm (Aein e) (Aeout e)
  box-e e = Agen-edge H e

  R-obj : List (Fin H.nV) → ObjTerm
  R-obj Rlist = unflatten (map H.vlab Rlist)

  -- Map-bridged `unflatten-++-≅`.
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

module _ (H : Hypergraph FlatGen)
         (K : FaithfulnessResidual)
         where
  private module H = Hypergraph H

  open ViewFrames H

  ----------------------------------------------------------------------
  -- ## Box / permute machinery for the proof of `block-bracket`.
  --
  -- `BT` is the block-tensor module at `H.vlab`; its `uf++` is
  -- DEFINITIONALLY the local `uf++` above.  `pvl` is `permute-via-vlab H.vlab`.
  ----------------------------------------------------------------------

  private
    module FM = Category FreeMonoidal
    open FM.HomReasoning
    open import Categories.Morphism.Reasoning FreeMonoidal
      using (cancelInner; cancelˡ; pullˡ; pullʳ)

    module BT = DTS.BlockTensor H.vlab

    -- The `vlab`-framed box-suffix reframe; `box-suffix-BNf` is its `Rblk = R`
    -- instance.
    module BBS = DTS.BlockBoxSuffix H.vlab

    pvl : {xs ys : List (Fin H.nV)} → xs Perm.↭ ys
        → HomTerm (unflatten (map H.vlab xs)) (unflatten (map H.vlab ys))
    pvl = permute-via-vlab H.vlab

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
    -- The `fire-mid` `subst₂` over the `sym (map-++ …)` boundaries is the
    -- `to`/`from`-subst turning the raw `unflatten-++-≅` into `BT.uf++`.
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

        -- Split the `subst₂` over `∘` at the two interior objects.
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
    -- `Bframed e rest` = the `uf++`-framed `(box e ⊗ id)`.
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
    -- composed with the outer `uf++`.
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
    -- ## L1 — box residual-naturality: a residual permute `ρ : rest ↭ rest'`
    -- slides through the box `box-e e` (which acts only on the front block).
    --
    --   Bframed e rest' ∘ pvl(++⁺ˡ (ein e) ρ)
    --     ≈ pvl(++⁺ˡ (eout e) ρ) ∘ Bframed e rest
    --
    -- Sound (no K): pure naturality of `⊗` and the `uf++` framing.
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

        -- `from-ei' ∘ to-ei' = id` cancellation in the middle.
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
    -- The sequentially-fired result differs from the both-at-front `Both a b`
    -- by the OUTPUT block-swap.  No K / `Unique` needed: pure σ-naturality +
    -- bifunctoriality + the σ↔permute bridge `σ-block-comm`.
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
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-refl ⟩
        ( to-eobeoa ∘ box-b⊗ ∘ from-eibeoa )
          ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) )
          ≈⟨ FM.assoc ⟩
        to-eobeoa
          ∘ ( ( box-b⊗ ∘ from-eibeoa )
            ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) ) )
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eobeoa
          ∘ ( box-b⊗
            ∘ ( from-eibeoa
              ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) ) ) )
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ expose ⟩
        to-eobeoa
          ∘ ( box-b⊗
            ∘ ( ( from-eibeoa ∘ ( pvl++c ∘ to-eoaeib ) )
              ∘ ( box-a⊗ ∘ from-eiaeib ) ) )
          -- MID' ≈ σ.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-σ ⟩∘⟨refl ⟩
        to-eobeoa
          ∘ ( box-b⊗ ∘ ( σ {Aeout a} {Aein b} ∘ ( box-a⊗ ∘ from-eiaeib ) ) )
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eobeoa
          ∘ ( ( box-b⊗ ∘ σ {Aeout a} {Aein b} ) ∘ ( box-a⊗ ∘ from-eiaeib ) )
          ≈⟨ refl⟩∘⟨ σ-nat-b ⟩∘⟨refl ⟩
        to-eobeoa
          ∘ ( ( σ {Aeout a} {Aeout b} ∘ (id {Aeout a} ⊗₁ box-e b) )
            ∘ ( box-a⊗ ∘ from-eiaeib ) )
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

        -- Reassociate so MID' and `box-a⊗ ∘ from-eiaeib` are the two top-level units.
        expose
          : from-eibeoa ∘ ( pvl++c ∘ ( to-eoaeib ∘ box-a⊗ ∘ from-eiaeib ) )
            ≈Term ( from-eibeoa ∘ ( pvl++c ∘ to-eoaeib ) ) ∘ ( box-a⊗ ∘ from-eiaeib )
        expose = ≈-Term-trans (refl⟩∘⟨ FM.sym-assoc) FM.sym-assoc

        -- The middle reduces to the bare braiding `σ` (σ-block-comm + cancel).
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

        -- σ-naturality.
        σ-nat-b
          : (box-e b ⊗₁ id {Aeout a}) ∘ σ {Aeout a} {Aein b}
            ≈Term σ {Aeout a} {Aeout b} ∘ (id {Aeout a} ⊗₁ box-e b)
        σ-nat-b = ≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ

        -- bifunctoriality.
        bifun
          : (id {Aeout a} ⊗₁ box-e b) ∘ (box-e a ⊗₁ id {Aein b})
            ≈Term box-e a ⊗₁ box-e b
        bifun = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ idˡ idʳ)

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
    -- `BT.uf++ (·++rest) R`.  Sound (no K): associativity / framing bookkeeping.
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
      -- `map-++ H.vlab` layers.
      whole-eq : ∀ (lBlk rgBlk R : List (Fin H.nV))
               → map H.vlab lBlk ++ (map H.vlab rgBlk ++ map H.vlab R)
                 ≡ map H.vlab ((lBlk ++ rgBlk) ++ R)
      whole-eq lBlk rgBlk R =
        trans (sym (++-assoc (map H.vlab lBlk) (map H.vlab rgBlk) (map H.vlab R)))
        (trans (cong (_++ map H.vlab R) (sym (map-++ H.vlab lBlk rgBlk)))
               (sym (map-++ H.vlab (lBlk ++ rgBlk) R)))

    -- `box-suffix` reframed into `BT.uf++`.
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
      BBS.box-suffix-framed eiBlk eoBlk rgBlk R g

    ----------------------------------------------------------------------
    -- `bframed-suffix` — the box on a COMPOUND residual `rest ++ R`,
    -- transported across the `++-assoc` boundary, equals the box on `rest`
    -- tensored with `id` on `R`, re-framed.  The framing primitive that lifts
    -- `both-as-fire` to a common residual `R` for the `block-bracket` assembly.
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
          -- collapse the stacked substs to a single subst, UIP-collapse onto
          -- box-suffix-BNf's LHS subst.
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
    -- ## `both-as-fire-R` — the residual-`R` lift of `both-as-fire`.
    --
    -- `both-as-fire` is at the BARE box residuals; here we lift it to a
    -- COMMON residual `R` carried under each box.  No K: pure ⊗-functoriality
    -- + the proven framing primitives.
    private
      -- The compound-residual block swaps, framed at `R` (a `++⁺ʳ R` of `++-comm`).
      ++R : ∀ {xs ys : List (Fin H.nV)} → xs Perm.↭ ys → (R : List (Fin H.nV))
          → xs ++ R Perm.↭ ys ++ R
      ++R p R = PermProp.++⁺ʳ R p

      -- Block-prefix cancellation.
      ++-cancelˡ : ∀ (xs : List (Fin H.nV)) {ys zs : List (Fin H.nV)}
                 → xs ++ ys Perm.↭ xs ++ zs → ys Perm.↭ zs
      ++-cancelˡ []       p = p
      ++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)

      -- `Bf-R e rest R` — box `e` framed at the COMPOUND residual `rest ++ R`,
      -- in the `(·++·)++R`-bracketed shape (the RHS of `bframed-suffix`).
      Bf-R : (e : Fin H.nE) (rest R : List (Fin H.nV))
           → HomTerm (unflatten (map H.vlab ((H.ein  e ++ rest) ++ R)))
                     (unflatten (map H.vlab ((H.eout e ++ rest) ++ R)))
      Bf-R e rest R =
        _≅_.to (BT.uf++ (H.eout e ++ rest) R)
        ∘ (Bframed e rest ⊗₁ id {R-obj R})
        ∘ _≅_.from (BT.uf++ (H.ein e ++ rest) R)

      -- A `subst₂ HomTerm` over `cong unflatten (cong (map vlab) ·)` list-
      -- equalities is conjugation by the `pvl`s of their `↭-reflexive`s.
      coh-subst₂
        : ∀ {As As' Bs Bs' : List (Fin H.nV)} (eA : As ≡ As') (eB : Bs ≡ Bs')
            (f : HomTerm (unflatten (map H.vlab As)) (unflatten (map H.vlab Bs)))
        → subst₂ HomTerm
            (cong unflatten (cong (map H.vlab) eA))
            (cong unflatten (cong (map H.vlab) eB)) f
          ≈Term pvl (Perm.↭-reflexive eB)
                ∘ ( f ∘ pvl (Perm.↭-reflexive (sym eA)) )
      coh-subst₂ refl refl f = ≈-Term-sym (≈-Term-trans idˡ idʳ)

    -- Sound (no K): `both-as-fire a b` tensored with `id {R}` and framed by
    -- the `uf++ … R` isos; the middle cancellations are `BT.frame-ext`, and
    -- `Core a b R` is recovered by `core≡both-framed`.
    both-as-fire-R
      : ∀ (a b : Fin H.nE) (R : List (Fin H.nV))
      → Bf-R b (H.eout a) R
          ∘ pvl (PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.ein b)))
          ∘ Bf-R a (H.ein b) R
        ≈Term pvl (PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.eout b)))
              ∘ Core a b R
    both-as-fire-R a b R = begin
        Bf-R b (H.eout a) R
          ∘ pvl (PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.ein b)))
          ∘ Bf-R a (H.ein b) R
          ≈⟨ refl⟩∘⟨ ≈-Term-sym
               (BT.frame-ext (H.eout a ++ H.ein b) (H.ein b ++ H.eout a) R
                  (PermProp.++-comm (H.eout a) (H.ein b)))
               ⟩∘⟨refl ⟩
        Bf-R b (H.eout a) R
          ∘ ( to-ba ∘ (pvl (PermProp.++-comm (H.eout a) (H.ein b)) ⊗₁ id {R-obj R}) ∘ from-ab )
          ∘ Bf-R a (H.ein b) R
          ≈⟨ telescope ⟩
        _≅_.to (BT.uf++ (H.eout b ++ H.eout a) R)
          ∘ ( ( Bframed b (H.eout a)
                  ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b))
                  ∘ Bframed a (H.ein b) ) ⊗₁ id {R-obj R} )
          ∘ _≅_.from (BT.uf++ (H.ein a ++ H.ein b) R)
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (both-as-fire a b) ≈-Term-refl ⟩∘⟨refl ⟩
        _≅_.to (BT.uf++ (H.eout b ++ H.eout a) R)
          ∘ ( ( pvl (PermProp.++-comm (H.eout a) (H.eout b)) ∘ Both a b ) ⊗₁ id {R-obj R} )
          ∘ _≅_.from (BT.uf++ (H.ein a ++ H.ein b) R)
          ≈⟨ refl⟩∘⟨ ⊗id-∘ (pvl (PermProp.++-comm (H.eout a) (H.eout b))) (Both a b) ⟩∘⟨refl ⟩
        _≅_.to (BT.uf++ (H.eout b ++ H.eout a) R)
          ∘ ( (pvl (PermProp.++-comm (H.eout a) (H.eout b)) ⊗₁ id {R-obj R})
              ∘ (Both a b ⊗₁ id {R-obj R}) )
          ∘ _≅_.from (BT.uf++ (H.ein a ++ H.ein b) R)
          ≈⟨ regroup-out ⟩
        ( _≅_.to (BT.uf++ (H.eout b ++ H.eout a) R)
            ∘ (pvl (PermProp.++-comm (H.eout a) (H.eout b)) ⊗₁ id {R-obj R})
            ∘ _≅_.from (BT.uf++ (H.eout a ++ H.eout b) R) )
          ∘ ( _≅_.to (BT.uf++ (H.eout a ++ H.eout b) R)
              ∘ (Both a b ⊗₁ id {R-obj R})
              ∘ _≅_.from (BT.uf++ (H.ein a ++ H.ein b) R) )
          ≈⟨ BT.frame-ext (H.eout a ++ H.eout b) (H.eout b ++ H.eout a) R
                (PermProp.++-comm (H.eout a) (H.eout b))
             ⟩∘⟨ ≈-Term-sym (core≡both-framed a b R) ⟩
        pvl (PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.eout b)))
          ∘ Core a b R ∎
      where
        to-ba   = _≅_.to   (BT.uf++ (H.ein b ++ H.eout a) R)
        from-ab = _≅_.from (BT.uf++ (H.eout a ++ H.ein b) R)

        ⊗id-∘ : ∀ {A B D} (h : HomTerm B D) (k : HomTerm A B)
              → (h ∘ k) ⊗₁ id {R-obj R} ≈Term (h ⊗₁ id) ∘ (k ⊗₁ id)
        ⊗id-∘ h k =
          ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

        Bb = Bframed b (H.eout a) ⊗₁ id {R-obj R}
        Sw = pvl (PermProp.++-comm (H.eout a) (H.ein b)) ⊗₁ id {R-obj R}
        Ba = Bframed a (H.ein b) ⊗₁ id {R-obj R}
        to-bb   = _≅_.to   (BT.uf++ (H.eout b ++ H.eout a) R)
        fr-bb   = _≅_.from (BT.uf++ (H.ein  b ++ H.eout a) R)
        fr-aa   = _≅_.from (BT.uf++ (H.ein  a ++ H.ein  b) R)
        to-ab   = _≅_.to   (BT.uf++ (H.eout a ++ H.ein  b) R)

        -- merge three `⊗ id` whiskers into (boxes) ⊗ id.
        merge3 : Bb ∘ Sw ∘ Ba
               ≈Term ( Bframed b (H.eout a)
                       ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b))
                       ∘ Bframed a (H.ein b) ) ⊗₁ id {R-obj R}
        merge3 =
          ≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym (⊗id-∘ _ _)))
            (≈-Term-sym (⊗id-∘ _ _))

        -- `M ∘ Bf-R a (ein b) R`: cancel the interior `from-ab ∘ to-ab = id`.
        glue-MBa
          : ( to-ba ∘ Sw ∘ from-ab ) ∘ Bf-R a (H.ein b) R
            ≈Term to-ba ∘ Sw ∘ Ba ∘ fr-aa
        glue-MBa =
          ≈-Term-trans FM.assoc
            (refl⟩∘⟨ (≈-Term-trans FM.assoc
              (refl⟩∘⟨ cancelˡ (_≅_.isoʳ (BT.uf++ (H.eout a ++ H.ein b) R)))))

        -- cancel the interior `fr-bb ∘ to-ba = id`.
        glue-Bb
          : Bf-R b (H.eout a) R ∘ ( to-ba ∘ Sw ∘ Ba ∘ fr-aa )
            ≈Term to-bb ∘ Bb ∘ Sw ∘ Ba ∘ fr-aa
        glue-Bb =
          ≈-Term-trans FM.assoc
            (refl⟩∘⟨ cancelInner (_≅_.isoʳ (BT.uf++ (H.ein b ++ H.eout a) R)))

        telescope
          : Bf-R b (H.eout a) R ∘ ( to-ba ∘ Sw ∘ from-ab ) ∘ Bf-R a (H.ein b) R
            ≈Term to-bb
                  ∘ ( ( Bframed b (H.eout a)
                        ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b))
                        ∘ Bframed a (H.ein b) ) ⊗₁ id {R-obj R} )
                  ∘ fr-aa
        telescope = begin
            Bf-R b (H.eout a) R ∘ ( to-ba ∘ Sw ∘ from-ab ) ∘ Bf-R a (H.ein b) R
              ≈⟨ refl⟩∘⟨ glue-MBa ⟩
            Bf-R b (H.eout a) R ∘ ( to-ba ∘ Sw ∘ Ba ∘ fr-aa )
              ≈⟨ glue-Bb ⟩
            to-bb ∘ Bb ∘ Sw ∘ Ba ∘ fr-aa
              ≈⟨ refl⟩∘⟨ regroup3 ⟩
            to-bb ∘ (Bb ∘ Sw ∘ Ba) ∘ fr-aa
              ≈⟨ refl⟩∘⟨ merge3 ⟩∘⟨refl ⟩
            to-bb
              ∘ ( ( Bframed b (H.eout a)
                    ∘ pvl (PermProp.++-comm (H.eout a) (H.ein b))
                    ∘ Bframed a (H.ein b) ) ⊗₁ id {R-obj R} )
              ∘ fr-aa ∎
          where
            regroup3 : Bb ∘ Sw ∘ Ba ∘ fr-aa ≈Term (Bb ∘ Sw ∘ Ba) ∘ fr-aa
            regroup3 =
              ≈-Term-trans (refl⟩∘⟨ FM.sym-assoc) FM.sym-assoc

        regroup-out
          : to-bb
              ∘ ( (pvl (PermProp.++-comm (H.eout a) (H.eout b)) ⊗₁ id {R-obj R})
                  ∘ (Both a b ⊗₁ id {R-obj R}) )
              ∘ fr-aa
            ≈Term ( to-bb
                    ∘ (pvl (PermProp.++-comm (H.eout a) (H.eout b)) ⊗₁ id {R-obj R})
                    ∘ _≅_.from (BT.uf++ (H.eout a ++ H.eout b) R) )
                  ∘ ( _≅_.to (BT.uf++ (H.eout a ++ H.eout b) R)
                      ∘ (Both a b ⊗₁ id {R-obj R})
                      ∘ fr-aa )
        regroup-out = begin
            to-bb ∘ (Sout ∘ BothC) ∘ fr-aa
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            to-bb ∘ Sout ∘ BothC ∘ fr-aa
              -- insert `from-eoeo ∘ to-eoeo = id` between Sout and BothC.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym idˡ ⟩
            to-bb ∘ Sout ∘ id ∘ BothC ∘ fr-aa
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym (_≅_.isoʳ (BT.uf++ (H.eout a ++ H.eout b) R)) ⟩∘⟨refl ⟩
            to-bb ∘ Sout ∘ (from-eoeo ∘ to-eoeo) ∘ BothC ∘ fr-aa
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            to-bb ∘ Sout ∘ from-eoeo ∘ to-eoeo ∘ BothC ∘ fr-aa
              ≈⟨ regroup-final ⟩
            ( to-bb ∘ Sout ∘ from-eoeo )
              ∘ ( to-eoeo ∘ BothC ∘ fr-aa ) ∎
          where
            Sout    = pvl (PermProp.++-comm (H.eout a) (H.eout b)) ⊗₁ id {R-obj R}
            BothC   = Both a b ⊗₁ id {R-obj R}
            to-eoeo = _≅_.to   (BT.uf++ (H.eout a ++ H.eout b) R)
            from-eoeo = _≅_.from (BT.uf++ (H.eout a ++ H.eout b) R)
            regroup-final
              : to-bb ∘ Sout ∘ from-eoeo ∘ to-eoeo ∘ BothC ∘ fr-aa
                ≈Term ( to-bb ∘ Sout ∘ from-eoeo ) ∘ ( to-eoeo ∘ BothC ∘ fr-aa )
            regroup-final =
              ≈-Term-sym (≈-Term-trans FM.assoc (refl⟩∘⟨ FM.assoc))

    ----------------------------------------------------------------------
    -- ## The per-box bridge connecting a box framed at the FIRING residual
    -- `s` (`Bframed e s`) to the same box framed at the COMMON residual `R`
    -- (`Bf-R e rest R`), through the residual permute `ρ : s ↭ rest ++ R`.
    -- Pure framing (no K): `bframed-suffix` + `coh-subst₂` + `box-resid-slide`.
    private
      -- `Bf-R e rest R` unfolded onto `Bframed e (rest++R)` conjugated by the
      -- `↭-reflexive (++-assoc …)` coercions.
      bfR-unfold
        : ∀ (e : Fin H.nE) (rest R : List (Fin H.nV))
        → Bf-R e rest R
          ≈Term pvl (Perm.↭-reflexive (sym (++-assoc (H.eout e) rest R)))
                ∘ ( Bframed e (rest ++ R)
                    ∘ pvl (Perm.↭-reflexive (sym (sym (++-assoc (H.ein e) rest R)))) )
      bfR-unfold e rest R =
        ≈-Term-trans (≈-Term-sym (bframed-suffix e rest R))
          (coh-subst₂ (sym (++-assoc (H.ein e) rest R))
                      (sym (++-assoc (H.eout e) rest R))
                      (Bframed e (rest ++ R)))

      -- `Bf-R e rest R` re-expressed onto the FIRING-residual box
      -- `Bframed e s`, conjugated by `pvl`s of permutes with Unique endpoints
      -- (`in-perm`/`out-perm`, reconciled below against `loc`/`vout-loc`).
      bfR-fire
        : ∀ (e : Fin H.nE) (s rest R : List (Fin H.nV)) (ρ : s Perm.↭ rest ++ R)
        → (us-in : Unique (H.ein e ++ s))
        → Bf-R e rest R
          ≈Term pvl (Perm.trans (PermProp.++⁺ˡ (H.eout e) ρ)
                       (Perm.↭-reflexive (sym (++-assoc (H.eout e) rest R))))
                ∘ ( Bframed e s
                    ∘ pvl (Perm.↭-sym
                             (Perm.trans (PermProp.++⁺ˡ (H.ein e) ρ)
                               (Perm.↭-reflexive (sym (++-assoc (H.ein e) rest R))))) )
      bfR-fire e s rest R ρ us-in = begin
          Bf-R e rest R
            ≈⟨ bfR-unfold e rest R ⟩
          pvl ro ∘ ( Bframed e (rest ++ R) ∘ pvl ri )
            -- reconcile `ri` (K at the Unique `ein e ++ (rest++R)`).
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ri≈ ⟩
          pvl ro ∘ ( Bframed e (rest ++ R)
                     ∘ ( pvl (PermProp.++⁺ˡ (H.ein e) ρ) ∘ pvl in-inv ) )
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          pvl ro ∘ ( ( Bframed e (rest ++ R) ∘ pvl (PermProp.++⁺ˡ (H.ein e) ρ) )
                     ∘ pvl in-inv )
            ≈⟨ refl⟩∘⟨ box-resid-slide e ρ ⟩∘⟨refl ⟩
          pvl ro ∘ ( ( pvl (PermProp.++⁺ˡ (H.eout e) ρ) ∘ Bframed e s )
                     ∘ pvl in-inv )
            ≈⟨ refl⟩∘⟨ FM.assoc ⟩
          pvl ro ∘ ( pvl (PermProp.++⁺ˡ (H.eout e) ρ)
                     ∘ ( Bframed e s ∘ pvl in-inv ) )
            ≈⟨ FM.sym-assoc ⟩
          ( pvl ro ∘ pvl (PermProp.++⁺ˡ (H.eout e) ρ) )
            ∘ ( Bframed e s ∘ pvl in-inv )
            ≈⟨ ≈-Term-refl ⟩
          pvl (Perm.trans (PermProp.++⁺ˡ (H.eout e) ρ) ro)
            ∘ ( Bframed e s ∘ pvl in-inv ) ∎
        where
          ro = Perm.↭-reflexive (sym (++-assoc (H.eout e) rest R))
          ri = Perm.↭-reflexive (sym (sym (++-assoc (H.ein e) rest R)))
          in-perm = Perm.trans (PermProp.++⁺ˡ (H.ein e) ρ)
                      (Perm.↭-reflexive (sym (++-assoc (H.ein e) rest R)))
          in-inv  = Perm.↭-sym in-perm
          -- reconciled by K at the Unique cod `ein e ++ (rest++R)`.
          ri≈ : pvl ri
                ≈Term pvl (PermProp.++⁺ˡ (H.ein e) ρ) ∘ pvl in-inv
          ri≈ =
            pvl-coh
              (SU.Unique-resp-↭ (PermProp.++⁺ˡ (H.ein e) ρ) us-in)
              ri
              (Perm.trans in-inv (PermProp.++⁺ˡ (H.ein e) ρ))

    ----------------------------------------------------------------------
    -- ## `block-bracket-pf` — the proof of the single residual.
    --
    -- Reconcile the FIRING-residual two-box composite (`fire-mid`) against the
    -- block normal form (the goal RHS), via `both-as-fire-R` + `bfR-fire`,
    -- with the locating permutes reconciled by `pvl-coh` (K) on the three
    -- Unique codomains (`us-sp`-image / `us-mid` / `us-cod`).
    block-bracket-pf
      : ∀ (a b : Fin H.nE)
          (sp : List (Fin H.nV))
          (s₁ : List (Fin H.nV)) (q-first  : sp Perm.↭ H.ein a ++ s₁)
          (s₂ : List (Fin H.nV)) (q-second : H.eout a ++ s₁ Perm.↭ H.ein b ++ s₂)
          (R  : List (Fin H.nV))
          (loc      : sp Perm.↭ (H.ein a ++ H.ein b) ++ R)
          (vout-loc : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂)
          (us-sp  : Unique sp)
          (us-mid : Unique (H.ein b ++ s₂))
          (us-cod : Unique (H.eout b ++ s₂))
      → ( fire-mid H b s₂ ∘ pvl q-second ∘ fire-mid H a s₁ ∘ pvl q-first )
        ≈Term ( pvl vout-loc ∘ _≅_.to (view-out≅ a b R) )
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ pvl loc )
    block-bracket-pf a b sp s₁ q-first s₂ q-second R loc vout-loc us-sp us-mid us-cod =
      begin
        fire-mid H b s₂ ∘ pvl q-second ∘ fire-mid H a s₁ ∘ pvl q-first
          ≈⟨ fire≈Bframed b s₂ ⟩∘⟨ refl⟩∘⟨ fire≈Bframed a s₁ ⟩∘⟨refl ⟩
        Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ pvl q-first
          -- `pvl q-first ≈ pvl in-inv-a ∘ pvl loc`  [K at the Unique `ein a ++ s₁`].
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ q-first≈ ⟩
        Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ ( pvl in-inv-a ∘ pvl loc )
          ≈⟨ regroup-in ⟩
        ( Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ pvl in-inv-a ) ∘ pvl loc
          ≈⟨ master ⟩∘⟨refl ⟩
        ( pvl vout-loc ∘ Core a b R ) ∘ pvl loc
          ≈⟨ FM.assoc ⟩
        pvl vout-loc ∘ ( Core a b R ∘ pvl loc )
          ≈⟨ ≈-Term-sym core-reassoc ⟩
        ( pvl vout-loc ∘ _≅_.to (view-out≅ a b R) )
          ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
          ∘ ( _≅_.from (view-in≅ a b R) ∘ pvl loc ) ∎
      where
        -- residual permutes from the locating permutes (block-prefix cancel).
        ρ₁ : s₁ Perm.↭ H.ein b ++ R
        ρ₁ = ++-cancelˡ (H.ein a)
               (Perm.trans (Perm.↭-sym q-first)
                 (Perm.trans loc (Perm.↭-reflexive (++-assoc (H.ein a) (H.ein b) R))))
        ρ₂ : s₂ Perm.↭ H.eout a ++ R
        ρ₂ = ++-cancelˡ (H.ein b)
               (Perm.trans (Perm.↭-sym q-second)
                 (Perm.trans (PermProp.++⁺ˡ (H.eout a) ρ₁)
                   (eo-shift)))
          where
            eo-shift : H.eout a ++ (H.ein b ++ R) Perm.↭ H.ein b ++ (H.eout a ++ R)
            eo-shift =
              Perm.trans (Perm.↭-sym (Perm.↭-reflexive (++-assoc (H.eout a) (H.ein b) R)))
                (Perm.trans (PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.ein b)))
                  (Perm.↭-reflexive (++-assoc (H.ein b) (H.eout a) R)))

        us-in-a : Unique (H.ein a ++ s₁)
        us-in-a = SU.Unique-resp-↭ q-first us-sp

        -- the `bfR-fire` data for the two boxes.
        ro-a = Perm.↭-reflexive (sym (++-assoc (H.eout a) (H.ein b) R))
        ro-b = Perm.↭-reflexive (sym (++-assoc (H.eout b) (H.eout a) R))
        out-a = Perm.trans (PermProp.++⁺ˡ (H.eout a) ρ₁) ro-a
        out-b = Perm.trans (PermProp.++⁺ˡ (H.eout b) ρ₂) ro-b
        in-perm-a = Perm.trans (PermProp.++⁺ˡ (H.ein a) ρ₁)
                      (Perm.↭-reflexive (sym (++-assoc (H.ein a) (H.ein b) R)))
        in-perm-b = Perm.trans (PermProp.++⁺ˡ (H.ein b) ρ₂)
                      (Perm.↭-reflexive (sym (++-assoc (H.ein b) (H.eout a) R)))
        in-inv-a = Perm.↭-sym in-perm-a
        in-inv-b = Perm.↭-sym in-perm-b

        σi = PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.ein b))
        σo = PermProp.++⁺ʳ R (PermProp.++-comm (H.eout a) (H.eout b))

        -- reconcile `q-first` with `trans loc in-inv-a` at the Unique `ein a ++ s₁`.
        q-first≈ : pvl q-first ≈Term pvl in-inv-a ∘ pvl loc
        q-first≈ = pvl-coh us-in-a q-first (Perm.trans loc in-inv-a)

        regroup-in
          : Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ ( pvl in-inv-a ∘ pvl loc )
            ≈Term ( Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ pvl in-inv-a ) ∘ pvl loc
        regroup-in =
          ≈-Term-sym
            (≈-Term-trans FM.assoc
              (refl⟩∘⟨ (≈-Term-trans FM.assoc
                (refl⟩∘⟨ FM.assoc))))

        core-reassoc
          : ( pvl vout-loc ∘ _≅_.to (view-out≅ a b R) )
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ pvl loc )
            ≈Term pvl vout-loc ∘ ( Core a b R ∘ pvl loc )
        core-reassoc = begin
            ( pvl vout-loc ∘ _≅_.to (view-out≅ a b R) )
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ pvl loc )
              ≈⟨ FM.assoc ⟩
            pvl vout-loc ∘ ( _≅_.to (view-out≅ a b R)
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ pvl loc ) )
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            pvl vout-loc ∘ ( _≅_.to (view-out≅ a b R)
              ∘ ( ((box-e a ⊗₁ box-e b) ⊗₁ id)
                  ∘ _≅_.from (view-in≅ a b R) ) ∘ pvl loc )
              ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            pvl vout-loc ∘ ( ( _≅_.to (view-out≅ a b R)
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ _≅_.from (view-in≅ a b R) ) ∘ pvl loc ) ∎

        -- `master` — the bracketed firing run equals `pvl vout-loc ∘ Core`.

        -- the two `bfR-fire` instances.
        bfa : Bf-R a (H.ein b) R
              ≈Term pvl out-a ∘ ( Bframed a s₁ ∘ pvl in-inv-a )
        bfa = bfR-fire a s₁ (H.ein b) R ρ₁ us-in-a

        bfb : Bf-R b (H.eout a) R
              ≈Term pvl out-b ∘ ( Bframed b s₂ ∘ pvl in-inv-b )
        bfb = bfR-fire b s₂ (H.eout a) R ρ₂ us-mid

        -- `MID : eout a ++ s₁ ↭ ein b ++ s₂`, grouped so `pvl MID` is the
        -- RIGHT-associated `pvl in-inv-b ∘ (pvl σi ∘ pvl out-a)`.  Reconciled
        -- with `q-second` at the Unique `ein b ++ s₂`.
        MID = Perm.trans (Perm.trans out-a σi) in-inv-b

        q-second≈ : pvl MID ≈Term pvl q-second
        q-second≈ = pvl-coh us-mid MID q-second

        -- substitute `bfR-fire` into `both-as-fire-R`-LHS, both sides
        -- re-associated onto the common fully-right-associated form.
        assembled
          : Bf-R b (H.eout a) R ∘ pvl σi ∘ Bf-R a (H.ein b) R
            ≈Term pvl out-b
                  ∘ ( Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a )
        assembled = begin
            Bf-R b (H.eout a) R ∘ pvl σi ∘ Bf-R a (H.ein b) R
              ≈⟨ bfb ⟩∘⟨ refl⟩∘⟨ bfa ⟩
            ( pvl out-b ∘ ( Bframed b s₂ ∘ pvl in-inv-b ) )
              ∘ pvl σi
              ∘ ( pvl out-a ∘ ( Bframed a s₁ ∘ pvl in-inv-a ) )
              ≈⟨ to-flat ⟩
            pvl out-b ∘ ( Bframed b s₂
              ∘ ( pvl in-inv-b ∘ ( pvl σi ∘ ( pvl out-a
              ∘ ( Bframed a s₁ ∘ pvl in-inv-a ) ) ) ) )
              ≈⟨ ≈-Term-sym from-flat ⟩
            pvl out-b
              ∘ ( Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a ) ∎
          where
            to-flat
              : ( pvl out-b ∘ ( Bframed b s₂ ∘ pvl in-inv-b ) )
                  ∘ pvl σi
                  ∘ ( pvl out-a ∘ ( Bframed a s₁ ∘ pvl in-inv-a ) )
                ≈Term pvl out-b ∘ ( Bframed b s₂
                  ∘ ( pvl in-inv-b ∘ ( pvl σi ∘ ( pvl out-a
                  ∘ ( Bframed a s₁ ∘ pvl in-inv-a ) ) ) ) )
            to-flat =
              ≈-Term-trans FM.assoc (refl⟩∘⟨ FM.assoc)
            -- `pvl MID = pvl in-inv-b ∘ (pvl σi ∘ pvl out-a)` (definitional).
            from-flat
              : pvl out-b
                  ∘ ( Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a )
                ≈Term pvl out-b ∘ ( Bframed b s₂
                  ∘ ( pvl in-inv-b ∘ ( pvl σi ∘ ( pvl out-a
                  ∘ ( Bframed a s₁ ∘ pvl in-inv-a ) ) ) ) )
            from-flat =
              refl⟩∘⟨ refl⟩∘⟨
                (≈-Term-trans FM.assoc (refl⟩∘⟨ FM.assoc))

        -- `master`: cancel `pvl out-b` and reconcile `q-second`/`vout-loc`.
        master
          : Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ pvl in-inv-a
            ≈Term pvl vout-loc ∘ Core a b R
        master = begin
            Bframed b s₂ ∘ pvl q-second ∘ Bframed a s₁ ∘ pvl in-inv-a
              -- replace `q-second` by `MID` (K, us-mid).
              ≈⟨ refl⟩∘⟨ ≈-Term-sym q-second≈ ⟩∘⟨refl ⟩
            Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a
              -- prepend `pvl (↭-sym out-b) ∘ pvl out-b = id` (K, us-cod).
              ≈⟨ ≈-Term-sym (cancel-out-b) ⟩
            pvl (Perm.↭-sym out-b)
              ∘ ( pvl out-b ∘ ( Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a ) )
              ≈⟨ refl⟩∘⟨ ≈-Term-sym assembled ⟩
            pvl (Perm.↭-sym out-b)
              ∘ ( Bf-R b (H.eout a) R ∘ pvl σi ∘ Bf-R a (H.ein b) R )
              ≈⟨ refl⟩∘⟨ both-as-fire-R a b R ⟩
            pvl (Perm.↭-sym out-b) ∘ ( pvl σo ∘ Core a b R )
              ≈⟨ FM.sym-assoc ⟩
            ( pvl (Perm.↭-sym out-b) ∘ pvl σo ) ∘ Core a b R
              ≈⟨ vout≈ ⟩∘⟨refl ⟩
            pvl vout-loc ∘ Core a b R ∎
          where
            -- `pvl (↭-sym out-b) ∘ pvl out-b ≈ id`  [K at the Unique `eout b ++ s₂`].
            cancel-out-b
              : pvl (Perm.↭-sym out-b)
                  ∘ ( pvl out-b ∘ ( Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a ) )
                ≈Term Bframed b s₂ ∘ pvl MID ∘ Bframed a s₁ ∘ pvl in-inv-a
            cancel-out-b =
              ≈-Term-trans FM.sym-assoc
                (≈-Term-trans
                  (∘-resp-≈ out-b-iso ≈-Term-refl)
                  idˡ)
              where
                out-b-iso : pvl (Perm.↭-sym out-b) ∘ pvl out-b ≈Term id
                out-b-iso =
                  pvl-coh us-cod (Perm.trans out-b (Perm.↭-sym out-b)) Perm.refl
            -- reconciled with `pvl vout-loc` (K, us-cod).
            vout≈ : pvl (Perm.↭-sym out-b) ∘ pvl σo ≈Term pvl vout-loc
            vout≈ = pvl-coh us-cod (Perm.trans σo (Perm.↭-sym out-b)) vout-loc

  ----------------------------------------------------------------------
  -- ## The single residual (scaffolding-stripped, block-symmetric).
  --
  -- For two edges `a`, `b` fired in order `a ∷ b` from a stack `sp` with
  -- locating permutes
  --
  --   q-first  : sp                  ↭ ein a ++ s₁
  --   q-second : eout a ++ s₁        ↭ ein b ++ s₂
  --   loc      : sp                  ↭ (ein a ++ ein b) ++ R
  --   vout-loc : (eout a ++ eout b) ++ R ↭ eout b ++ s₂
  --
  -- the located-firing composite factors as the 3-block normal form.  This
  -- is symmetric under swapping (a,b), so the SAME field serves both orders.
  --
  -- SOUNDNESS: the `Unique` hypotheses (`us-sp` / `us-cod`) are NOT
  -- decorative — without them the equation is FALSE-as-stated.  A proof must
  -- reconcile the FIRING locating permutes against the BLOCK locating
  -- permutes; the only device that equates two such `↭`-derivations under
  -- `permute-via-vlab` is the Kelly keystone, which holds ONLY when the
  -- Fin-level codomain is `Unique` (the unrestricted statement is FALSE).
  --   * `us-sp` gates the INPUT reconciliation (`q-first`/`q-second`/`loc`
  --     have `↭`-images of `sp` as codomains).
  --   * `us-cod` gates the OUTPUT reconciliation (`vout-loc`'s codomain is
  --     the FINAL stack, whose freshness is NOT derivable from `us-sp`).
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
            (us-mid : Unique (H.ein b ++ s₂))
            (us-cod : Unique (H.eout b ++ s₂))
        → ( fire-mid H b s₂ ∘ permute-via-vlab H.vlab q-second
              ∘ fire-mid H a s₁ ∘ permute-via-vlab H.vlab q-first )
          ≈Term ( permute-via-vlab H.vlab vout-loc ∘ _≅_.to (view-out≅ a b R) )
                ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
                ∘ ( _≅_.from (view-in≅ a b R) ∘ permute-via-vlab H.vlab loc )

  nf-bracket-proof : BlockBracket
  nf-bracket-proof = record { block-bracket = block-bracket-pf }

  ----------------------------------------------------------------------
  -- ## The generic block-normal-form factorisation.  Given the single
  -- residual, the located-firing factorisation holds for arbitrary locating
  -- permutes.  Symmetric under swapping the two blocks, so it serves both
  -- `nf₁` (order `e ∷ e'`) and `nf₂` (order `e' ∷ e`).
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
          (us-mid : Unique (H.ein b ++ s₂))
          (us-cod : Unique (H.eout b ++ s₂))
      → ( fire-mid H b s₂ ∘ permute-via-vlab H.vlab q-second
            ∘ fire-mid H a s₁ ∘ permute-via-vlab H.vlab q-first )
        ≈Term ( permute-via-vlab H.vlab vout-loc ∘ _≅_.to (view-out≅ a b R) )
              ∘ ((box-e a ⊗₁ box-e b) ⊗₁ id)
              ∘ ( _≅_.from (view-in≅ a b R) ∘ permute-via-vlab H.vlab loc )
    block-nf-generic = block-bracket

    ----------------------------------------------------------------------
    -- ## The two instantiations, recovering the `nf₂-eq′` / `nf₁-eq′` types
    -- (modulo `Comb.SimLoc` supplying `Rlist`, `loc₁`/`loc₂`,
    -- `vout-loc₁`/`vout-loc₂`).  Takes the `dih`/`lin` parameters needed to
    -- build `Comb.SimLoc` exactly as `FireMidInterchange` does.
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

      -- `nf₂-eq′`: the e'-first order.  Blocks `a = e'`, `b = e`, `s₁ = r₂'`,
      -- `s₂ = r₁'`, `loc = loc₂`, `vout-loc = vout-loc₂`.
      nf₂-eq-derived
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
      nf₂-eq-derived {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid us-cod =
        block-nf-generic e' e sp r₂' p₂' r₁' p₁' Rlist loc₂ vout-loc₂ us-sp us-mid us-cod
        where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')

      -- `nf₁-eq′`: the e-first order (the MIRROR).  Blocks `a = e`, `b = e'`,
      -- `s₁ = r₁`, `s₂ = r₂`, `loc = loc₁`, `vout-loc = vout-loc₁`.
      nf₁-eq-derived
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
      nf₁-eq-derived {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-mid us-cod =
        block-nf-generic e e' sp r₁ p₁ r₂ p₂ Rlist loc₁ vout-loc₁ us-sp us-mid us-cod
        where open Comb.SimLoc (SL inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
