{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Towards the UNPRUNED `⊗` shape residual `decode-⊗-shape-inner` — the tensor
-- analogue of `Sub/DecodeComposeShape.agda`.  Target statement (the exact
-- `DecodeShape.DecodeShapeResiduals.decode-⊗-shape-inner` field type):
--
--   decode (f ⊗₁ g)
--     ≈Term to(unflatten-++-≅ (flatten B) (flatten D))
--            ∘ (decode f ⊗₁ decode g)
--            ∘ from(unflatten-++-≅ (flatten A) (flatten C))
--
-- This file proves the SHARED INFRASTRUCTURE and the genuinely-novel
-- permute-level block-tensor decomposition `BlockTensor.pvv-block-tensor`
-- (the `_⊗₁_` analogue of the `∘`-case final-permute collapse), all
-- postulate-free over `objUIP` + `K : FaithfulnessResidual`:
--
--   * `BlockTensor.pvv-block-tensor` — PROVEN, postulate-free:
--       `pvl (++⁺ p q) ≈ to(uf++ bs ds) ∘ (pvl p ⊗₁ pvl q) ∘ from(uf++ as cs)`.
--     Combines `FireMidEquivariant.permute-++⁺ˡ-slide` (left `++⁺ˡ` slide)
--     with `BlockNFBraid.frame-ext` (right `++⁺ʳ` slide), the middle
--     iso-cancellation, and `⊗`-interchange.  This is the tensor twin of the
--     `∘`-case `PermuteCoherenceK` final-permute collapse.
--   * `BlockTensor.pvv-++⁺ˡ-slide` — PROVEN: the vlab-bridged left slide.
--   * `BoxAssoc.box-suffix` / `BoxAssoc.box-prefix` — PROVEN, postulate-free:
--     the two per-edge `box-of` reassociations.  `box-suffix` pulls an
--     untouched far suffix `R` out of a front-acting box's residual as
--     `(box … restG) ⊗₁ id_R`; `box-prefix` (its mirror) pulls an untouched
--     left prefix `P` out of a P-prefixed right-acting box as
--     `(P-prefixed box on einR) ⊗₁ id_restK`.  Both are Mac-Lane coherences
--     (⊗-functoriality + `α-comm` + `c-iso-assoc-from`/`-to` + bifunctor
--     mid-collapse); `box-prefix` is the term-companion per-edge step for
--     the K-block factorization, `box-suffix` for the G-block.
--   * `BoxAssoc.box-braid` — PROVEN, postulate-free: the σ-mirror of
--     `box-suffix`.  A FRONT-acting box on residual `P ++ rest` factors as
--     the same box held AFTER the prefix `P` (`id {U P} ⊗₁ box-of … rest g`),
--     conjugated by the block-swap braids `σ-out`/`σ-in` (explicit composites
--     of the braiding `σ` and the `unflatten-++-≅` framing).  The move is the
--     PROVEN ONE-BOX symmetry-naturality `σ∘[f⊗g]≈[g⊗f]∘σ` (the single
--     generator slid past the identity block) + `σ∘σ≈id` + α-coherence
--     framing — the `N`+`M` content, NOT the two-box `nf-bracket` kernel.
--     This is the per-edge step that unblocks the K-side induction.
--   * `EmbedData.{TG,TK}` — the G-/K-side `TermEmbed` gate instances
--     (φ = injL / injR, ψ = _↑ˡ K.nE / G.nE ↑ʳ_).
--   * `decode-attempt-extract`, `Linear⇒cod-Unique` — the `DecodeComposeShape`
--     analogues.
--
-- The target `decode-⊗-shape-inner` is assembled in this file (see the
-- `## The FINAL ⊗ assembly` section).  Unlike the `∘` case — where
-- `C.dom = map injL G.dom` is a PURE φ-image and the gate applies directly —
-- the `⊗` blocks run on the DISJOINT MIXED dom
-- `map injL G.dom ++ map injR K.dom`, so each block term is first sliced as
-- `(canonical run ⊗₁ id)` (resp. `(id ⊗₁ canonical run)`) by a per-edge
-- `box-of`-suffix/-prefix `unflatten-++-≅` coherence induction before the gate
-- and `pvv-block-tensor` apply.  NO postulate, NO hole in this file.
--
-- Parameterised by `objUIP` and `K : FaithfulnessResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hTensor
        ; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL; map-via-inj; map-via-raise)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; process-all-edges
        ; decode-attempt; extract-exact)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; decode-attempt-Linear
        ; process-edges-↑ˡ-on-mixed; process-edges-↑ʳ-on-perm
        ; edge-step-↑ˡ-on-mixed; edge-step-↑ˡ-on-mixed-just
        ; edge-step-↑ˡ-on-mixed-nothing
        ; edge-step-↑ʳ-on-mixed-just; edge-step-↑ʳ-on-mixed-nothing
        ; edge-step-↑ʳ-on-perm)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↑ˡ-on-mixed-just; extract-prefix-↑ˡ-on-mixed-nothing
        ; extract-prefix-via-injective-just; extract-prefix-via-injective-nothing
        ; extract-prefix-↑ʳ-on-mixed-just; extract-prefix-↑ʳ-on-mixed-nothing
        ; extract-prefix-↭-residual; extract-prefix-↭-nothing)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (module TermEmbed; pe-term-++; pe-stack-++)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidEquivariant sig as FME
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData as BNB
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData as BNV
open import Categories.APROP.Hypergraph.Completeness.Discharge.CIsoAssocFromCons sig
  using (c-iso-assoc-from)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of
        ; edge-step-graph)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as AllProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-cong; trans-reflʳ; cong-∘)

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using ( ≡⇒≈Term
        ; subst₂-FlatGen-cancel; subst₂-FlatGen-cancel′
        ; subst₂-HomTerm-irrel; subst₂-HomTerm-∘; subst₂-resp-≈Term
        ; subst₂-HomTerm-∘-dist; subst₂-⊗₁-dist
        ; permute-subst₂
        ; pvv-relabel
        ; Linear⇒cod-Unique; decode-attempt-extract )

private
  module FM = Category FreeMonoidal

  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

  -- Generic middle-iso cancellation, shared by the `uf++`-framed block
  -- ladders (`BlockTensor.pvv-block-tensor`'s and `BlockFactor`'s
  -- `head-factor` / `head-factor-K` / `gblock-factor` / `KClean-cons`):
  -- two 3-fold composites sharing a middle iso `Fm ∘ Tm ≈ id` cancel it,
  -- leaving `To ∘ M₁ ∘ M₂ ∘ Ff`.  Pure associativity + the iso + `idˡ`;
  -- it makes no assumption about `M₁`/`M₂` (the `⊗₁`-merge tail, which
  -- differs per site, stays inline at the call sites).
  cancel-mid-iso
    : ∀ {A₀ A₁ A₂ A₃ A₄ A₅ : ObjTerm}
        (To : HomTerm A₄ A₅) (M₁ : HomTerm A₂ A₄) (Fm : HomTerm A₃ A₂)
        (Tm : HomTerm A₂ A₃) (M₂ : HomTerm A₁ A₂) (Ff : HomTerm A₀ A₁)
    → FM._∘_ Fm Tm ≈Term FM.id
    → FM._∘_ (FM._∘_ To (FM._∘_ M₁ Fm)) (FM._∘_ Tm (FM._∘_ M₂ Ff))
      ≈Term FM._∘_ To (FM._∘_ M₁ (FM._∘_ M₂ Ff))
  cancel-mid-iso To M₁ Fm Tm M₂ Ff m-iso =
    let open FM.HomReasoning in
    begin
      (To ∘ M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
        ≈⟨ FM.assoc ⟩
      To ∘ (M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      To ∘ M₁ ∘ Fm ∘ Tm ∘ M₂ ∘ Ff
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      To ∘ M₁ ∘ (Fm ∘ Tm) ∘ M₂ ∘ Ff
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ m-iso ⟩∘⟨refl ⟩
      To ∘ M₁ ∘ id ∘ M₂ ∘ Ff
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
      To ∘ M₁ ∘ M₂ ∘ Ff ∎

  -- `unflatten-++-≅`'s `to`/`from` transported along block-list equalities.
  to-uf-cong
    : ∀ {Xs Xs' Ys Ys' : List X} (pX : Xs ≡ Xs') (pY : Ys ≡ Ys')
    → subst₂ HomTerm (cong₂ _⊗₀_ (cong unflatten pX) (cong unflatten pY))
                     (cong unflatten (cong₂ _++_ pX pY))
        (_≅_.to (unflatten-++-≅ Xs Ys))
      ≡ _≅_.to (unflatten-++-≅ Xs' Ys')
  to-uf-cong refl refl = refl

  from-uf-cong
    : ∀ {Xs Xs' Ys Ys' : List X} (pX : Xs ≡ Xs') (pY : Ys ≡ Ys')
    → subst₂ HomTerm (cong unflatten (cong₂ _++_ pX pY))
                     (cong₂ _⊗₀_ (cong unflatten pX) (cong unflatten pY))
        (_≅_.from (unflatten-++-≅ Xs Ys))
      ≡ _≅_.from (unflatten-++-≅ Xs' Ys')
  from-uf-cong refl refl = refl

--------------------------------------------------------------------------------
-- ## The block-tensor decomposition of `permute`.
--
-- `permute (++⁺ p q)` slides through `unflatten-++-≅` as the tensor
-- `permute p ⊗₁ permute q`.  We build this from the LEFT slide
-- (`FME.permute-++⁺ˡ-slide`) and a RIGHT slide proved here by induction on
-- the `↭`-derivation, then compose them through the middle iso-cancellation
-- and `⊗`-interchange.

module BlockTensor
  {n : ℕ} (vlab : Fin n → X)
  where
  open FM.HomReasoning

  pvl : {xs ys : List (Fin n)} → xs Perm.↭ ys
      → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
  pvl = permute-via-vlab vlab

  uf++ : (As Bs : List (Fin n))
       → unflatten (map vlab (As ++ Bs))
         ≅ unflatten (map vlab As) ⊗₀ unflatten (map vlab Bs)
  uf++ = BNB.uf++ vlab

  R-obj : List (Fin n) → ObjTerm
  R-obj cs = unflatten (map vlab cs)

  frame-ext
    : (es fs cs : List (Fin n)) (P : es Perm.↭ fs)
    → _≅_.to (uf++ fs cs) ∘ (pvl P ⊗₁ id {A = R-obj cs}) ∘ _≅_.from (uf++ es cs)
      ≈Term pvl (PermProp.++⁺ʳ cs P)
  frame-ext = BNB.frame-ext vlab

  ------------------------------------------------------------------------
  -- vlab-bridged left slide `pvv-++⁺ˡ`, built from `FME.permute-++⁺ˡ-slide`
  -- + the `map⁺-++⁺ˡ`/`map-++` reconciliation (mirrors BlockNFBraid's
  -- `pvv-++⁺ʳ` + `frame-ext` for the right side, reusing BNB's `to-subst₂-≅`
  -- / `from-subst₂-≅` / `subst₂-∘-split` helpers).
  private
    -- `permute-via-vlab vlab (++⁺ˡ ws q)` re-expressed via the X-level
    -- `permute (++⁺ˡ (map vlab ws) (map⁺ vlab q))`, transported along
    -- `sym (map-++ vlab ws ·)`.
    pvv-++⁺ˡ-≡
      : ∀ (ws : List (Fin n)) {as bs : List (Fin n)} (q : as Perm.↭ bs)
      → pvl (PermProp.++⁺ˡ ws q)
        ≡ subst₂ HomTerm
            (cong unflatten (sym (map-++ vlab ws as)))
            (cong unflatten (sym (map-++ vlab ws bs)))
            (permute (PermProp.++⁺ˡ (map vlab ws) (PermProp.map⁺ vlab q)))
    pvv-++⁺ˡ-≡ ws {as} {bs} q =
      trans (cong permute (FME.map⁺-++⁺ˡ vlab ws q))
            (sym (permute-subst₂ (sym (map-++ vlab ws as)) (sym (map-++ vlab ws bs))
                    (PermProp.++⁺ˡ (map vlab ws) (PermProp.map⁺ vlab q))))

  -- vlab-bridged LEFT slide.
  pvv-++⁺ˡ-slide
    : ∀ (ws : List (Fin n)) {as bs : List (Fin n)} (q : as Perm.↭ bs)
    → pvl (PermProp.++⁺ˡ ws q)
      ≈Term _≅_.to (uf++ ws bs) ∘ (id {A = R-obj ws} ⊗₁ pvl q) ∘ _≅_.from (uf++ ws as)
  pvv-++⁺ˡ-slide ws {as} {bs} q = begin
    pvl (PermProp.++⁺ˡ ws q)
      ≈⟨ ≡⇒≈Term (pvv-++⁺ˡ-≡ ws q) ⟩
    subst₂ HomTerm pAs pBs (permute (PermProp.++⁺ˡ (map vlab ws) (PermProp.map⁺ vlab q)))
      ≈⟨ BNB.subst₂-resp-≈ pAs pBs
           (FME.permute-++⁺ˡ-slide (map vlab ws) (PermProp.map⁺ vlab q)) ⟩
    subst₂ HomTerm pAs pBs (rawTO ∘ ((id ⊗₁ permute (PermProp.map⁺ vlab q)) ∘ rawFROM))
      ≈⟨ ≡⇒≈Term (BNB.subst₂-∘-split pAs pBs
                    rawTO ((id ⊗₁ permute (PermProp.map⁺ vlab q)) ∘ rawFROM)) ⟩
    subst₂ HomTerm refl pBs rawTO
      ∘ subst₂ HomTerm pAs refl ((id ⊗₁ permute (PermProp.map⁺ vlab q)) ∘ rawFROM)
      ≈⟨ ∘-resp-≈ (≡⇒≈Term to-eq)
           (≈-Term-trans
             (≡⇒≈Term (BNB.subst₂-∘-split pAs refl
                         (id ⊗₁ permute (PermProp.map⁺ vlab q)) rawFROM))
             (∘-resp-≈ ≈-Term-refl (≡⇒≈Term from-eq))) ⟩
    _≅_.to (uf++ ws bs) ∘ ((id ⊗₁ pvl q) ∘ _≅_.from (uf++ ws as)) ∎
    where
      pAs   = cong unflatten (sym (map-++ vlab ws as))
      pBs   = cong unflatten (sym (map-++ vlab ws bs))
      rawTO   = _≅_.to   (unflatten-++-≅ (map vlab ws) (map vlab bs))
      rawFROM = _≅_.from (unflatten-++-≅ (map vlab ws) (map vlab as))

      to-eq : subst₂ HomTerm refl pBs rawTO ≡ _≅_.to (uf++ ws bs)
      to-eq = sym (BNB.to-subst₂-≅
                     (cong unflatten (sym (map-++ vlab ws bs)))
                     (unflatten-++-≅ (map vlab ws) (map vlab bs)))

      from-eq : subst₂ HomTerm pAs refl rawFROM ≡ _≅_.from (uf++ ws as)
      from-eq = sym (BNB.from-subst₂-≅
                       (cong unflatten (sym (map-++ vlab ws as)))
                       (unflatten-++-≅ (map vlab ws) (map vlab as)))

  ------------------------------------------------------------------------
  -- THE BLOCK-TENSOR DECOMPOSITION.
  --
  --   pvl (++⁺ p q)
  --     ≈ to(uf++ bs ds) ∘ (pvl p ⊗₁ pvl q) ∘ from(uf++ as cs)
  --
  -- `++⁺ p q = trans (++⁺ʳ cs p) (++⁺ˡ bs q)`, so
  -- `pvl (++⁺ p q) = pvl (++⁺ˡ bs q) ∘ pvl (++⁺ʳ cs p)`.  Slide each, cancel
  -- the middle `from(uf++ bs cs) ∘ to(uf++ bs cs) = id`, interchange.
  pvv-block-tensor
    : ∀ {as bs cs ds : List (Fin n)} (p : as Perm.↭ bs) (q : cs Perm.↭ ds)
    → pvl (PermProp.++⁺ p q)
      ≈Term _≅_.to (uf++ bs ds) ∘ (pvl p ⊗₁ pvl q) ∘ _≅_.from (uf++ as cs)
  pvv-block-tensor {as} {bs} {cs} {ds} p q = begin
    pvl (PermProp.++⁺ˡ bs q) ∘ pvl (PermProp.++⁺ʳ cs p)
      ≈⟨ ∘-resp-≈ (pvv-++⁺ˡ-slide bs q) (≈-Term-sym (frame-ext as bs cs p)) ⟩
    (to-bd ∘ (id ⊗₁ pvl q) ∘ from-bc)
      ∘ (to-bc ∘ (pvl p ⊗₁ id) ∘ from-ac)
      ≈⟨ cancel-mid ⟩
    to-bd ∘ (id ⊗₁ pvl q) ∘ (pvl p ⊗₁ id) ∘ from-ac
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    to-bd ∘ ((id ⊗₁ pvl q) ∘ (pvl p ⊗₁ id)) ∘ from-ac
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    to-bd ∘ ((id ∘ pvl p) ⊗₁ (pvl q ∘ id)) ∘ from-ac
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ idʳ ⟩∘⟨refl ⟩
    to-bd ∘ (pvl p ⊗₁ pvl q) ∘ from-ac ∎
    where
      to-bd = _≅_.to   (uf++ bs ds)
      from-bc = _≅_.from (uf++ bs cs)
      to-bc = _≅_.to   (uf++ bs cs)
      from-ac = _≅_.from (uf++ as cs)

      cancel-mid
        : (to-bd ∘ (id ⊗₁ pvl q) ∘ from-bc) ∘ (to-bc ∘ (pvl p ⊗₁ id) ∘ from-ac)
          ≈Term to-bd ∘ (id ⊗₁ pvl q) ∘ (pvl p ⊗₁ id) ∘ from-ac
      cancel-mid =
        cancel-mid-iso to-bd (id ⊗₁ pvl q) from-bc to-bc (pvl p ⊗₁ id) from-ac
          (_≅_.isoʳ (uf++ bs cs))

--------------------------------------------------------------------------------
-- ## Embedding data for `hTensor G K`.
--
-- For fixed `G K`, the tensor `C = hTensor G K` admits two injective,
-- label-preserving embeddings of the SUB-hypergraphs:
--
--   * G-side : φ = injL,  ψ = _↑ˡ K.nE   (the `eG ↑ˡ K.nE` edges).
--   * K-side : φ = injR,  ψ = G.nE ↑ʳ_   (the `G.nE ↑ʳ eK` edges).
--
-- We package each as the `TermEmbed` parameters via the hTensor-impl
-- reduction lemmas, so `process-edges-term-emb` applies.

module EmbedData
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  (G K : Hypergraph FlatGen)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open FA.hTensor-impl G K

  C-hg : Hypergraph FlatGen
  C-hg = hTensor G K

  ------------------------------------------------------------------------
  -- G-side embedding: φ = injL, ψ = _↑ˡ K.nE, H = G, J = C.
  ------------------------------------------------------------------------

  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  atom-einG : ∀ eG → map C.vlab (C.ein (ψG eG)) ≡ map G.vlab (G.ein eG)
  atom-einG eG = trans (cong (map vlab-c) (ein-c-inj₁-red eG))
                       (sym (map-via-inj vlab-injL (G.ein eG)))

  atom-eoutG : ∀ eG → map C.vlab (C.eout (ψG eG)) ≡ map G.vlab (G.eout eG)
  atom-eoutG eG = trans (cong (map vlab-c) (eout-c-inj₁-red eG))
                        (sym (map-via-inj vlab-injL (G.eout eG)))

  ψ-elabG : ∀ eG → subst₂ FlatGen (atom-einG eG) (atom-eoutG eG) (C.elab (ψG eG))
                 ≡ G.elab eG
  ψ-elabG eG =
    trans (subst₂-FlatGen-cancel
             (cong (map vlab-c) (ein-c-inj₁-red eG))
             (cong (map vlab-c) (eout-c-inj₁-red eG))
             (map-via-inj vlab-injL (G.ein eG))
             (map-via-inj vlab-injL (G.eout eG))
             (elab-c (eG ↑ˡ K.nE)))
          (trans (cong (subst₂ FlatGen
                          (sym (map-via-inj vlab-injL (G.ein eG)))
                          (sym (map-via-inj vlab-injL (G.eout eG))))
                       (elab-c-inj₁ eG))
                 (subst₂-FlatGen-cancel′
                    (map-via-inj vlab-injL (G.ein eG))
                    (map-via-inj vlab-injL (G.eout eG))
                    (G.elab eG)))

  module TG = TermEmbed {H = G} {J = hTensor G K} objUIP Kf
                injL (λ {x} {y} → ↑ˡ-injective K.nV x y)
                vlab-injL
                ψG ein-c-inj₁-red eout-c-inj₁-red
                atom-einG atom-eoutG ψ-elabG

  ------------------------------------------------------------------------
  -- K-side embedding: φ = injR, ψ = G.nE ↑ʳ_, H = K, J = C.
  ------------------------------------------------------------------------

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  atom-einK : ∀ eK → map C.vlab (C.ein (ψK eK)) ≡ map K.vlab (K.ein eK)
  atom-einK eK = trans (cong (map vlab-c) (ein-c-inj₂-red eK))
                       (sym (map-via-raise vlab-injR (K.ein eK)))

  atom-eoutK : ∀ eK → map C.vlab (C.eout (ψK eK)) ≡ map K.vlab (K.eout eK)
  atom-eoutK eK = trans (cong (map vlab-c) (eout-c-inj₂-red eK))
                        (sym (map-via-raise vlab-injR (K.eout eK)))

  ψ-elabK : ∀ eK → subst₂ FlatGen (atom-einK eK) (atom-eoutK eK) (C.elab (ψK eK))
                 ≡ K.elab eK
  ψ-elabK eK =
    trans (subst₂-FlatGen-cancel
             (cong (map vlab-c) (ein-c-inj₂-red eK))
             (cong (map vlab-c) (eout-c-inj₂-red eK))
             (map-via-raise vlab-injR (K.ein eK))
             (map-via-raise vlab-injR (K.eout eK))
             (elab-c (G.nE ↑ʳ eK)))
          (trans (cong (subst₂ FlatGen
                          (sym (map-via-raise vlab-injR (K.ein eK)))
                          (sym (map-via-raise vlab-injR (K.eout eK))))
                       (elab-c-inj₂ eK))
                 (subst₂-FlatGen-cancel′
                    (map-via-raise vlab-injR (K.ein eK))
                    (map-via-raise vlab-injR (K.eout eK))
                    (K.elab eK)))

  module TK = TermEmbed {H = K} {J = hTensor G K} objUIP Kf
                injR (λ {x} {y} → ↑ʳ-injective G.nV x y)
                vlab-injR
                ψK ein-c-inj₂-red eout-c-inj₂-red
                atom-einK atom-eoutK ψ-elabK

--------------------------------------------------------------------------------
-- ## The BOX-SUFFIX / BOX-PREFIX `unflatten-++-≅` reassociations.
--
-- The genuinely-novel `⊗`-case content: a single edge's `box-of` factor
-- on a residual list of the form `restG ++ R` (resp. `P ++ restK`) factors,
-- modulo `unflatten-++-≅` framing, as `(box-of … restG …) ⊗₁ id` (resp.
-- `id ⊗₁ (box-of … restK …)`).  Both are Mac-Lane coherences built from
-- the proven `c-iso-assoc-from` (the `from`-side associativity of
-- `unflatten-++-≅`) and its `to`-side dual derived here.

module BoxAssoc where
  open FM.HomReasoning

  sym² : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
  sym² refl = refl

  -- `from`-side associativity (the proven kernel, with the trailing
  -- `subst` made explicit).
  assoc-from = c-iso-assoc-from

  -- The `to`-side dual, derived from `c-iso-assoc-from` by composite
  -- inversion.  For `Lhs ≈ Rhs` with both composites of isos, the
  -- inverses satisfy `Lhsinv ≈ Rhsinv`; we prove it by
  -- `Lhsinv ≈ Rhsinv ∘ Rhs ∘ Lhsinv ≈ Rhsinv ∘ Lhs ∘ Lhsinv ≈ Rhsinv`.
  c-iso-assoc-to
    : ∀ xs₁ xs₂ ys
    → _≅_.to (unflatten-++-≅ (xs₁ ++ xs₂) ys)
      ∘ (_≅_.to (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
      ∘ α⇐ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
    ≈Term subst (λ z → HomTerm (unflatten z) (unflatten ((xs₁ ++ xs₂) ++ ys)))
                (++-assoc xs₁ xs₂ ys) id
          ∘ _≅_.to (unflatten-++-≅ xs₁ (xs₂ ++ ys))
          ∘ (id {unflatten xs₁} ⊗₁ _≅_.to (unflatten-++-≅ xs₂ ys))
  c-iso-assoc-to xs₁ xs₂ ys = begin
    Lhsinv
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ Lhsinv
      ≈⟨ ≈-Term-sym RhsinvRhs ⟩∘⟨refl ⟩
    (Rhsinv ∘ Rhs) ∘ Lhsinv
      ≈⟨ (refl⟩∘⟨ ≈-Term-sym (assoc-from xs₁ xs₂ ys)) ⟩∘⟨refl ⟩
    (Rhsinv ∘ Lhs) ∘ Lhsinv
      ≈⟨ FM.assoc ⟩
    Rhsinv ∘ (Lhs ∘ Lhsinv)
      ≈⟨ refl⟩∘⟨ LhsLhsinv ⟩
    Rhsinv ∘ id
      ≈⟨ idʳ ⟩
    Rhsinv ∎
    where
      U₁  = unflatten xs₁
      U₂  = unflatten xs₂
      Uys = unflatten ys

      from₁₂   = _≅_.from (unflatten-++-≅ xs₁ xs₂)
      to₁₂     = _≅_.to   (unflatten-++-≅ xs₁ xs₂)
      from₁₂ys = _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
      to₁₂ys   = _≅_.to   (unflatten-++-≅ (xs₁ ++ xs₂) ys)
      from₂₃   = _≅_.from (unflatten-++-≅ xs₂ ys)
      to₂₃     = _≅_.to   (unflatten-++-≅ xs₂ ys)
      from₁₂₃  = _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
      to₁₂₃    = _≅_.to   (unflatten-++-≅ xs₁ (xs₂ ++ ys))

      e   = ++-assoc xs₁ xs₂ ys
      s-id : HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten (xs₁ ++ (xs₂ ++ ys)))
      s-id = subst (λ z → HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten z)) e id
      s-id⁻ : HomTerm (unflatten (xs₁ ++ (xs₂ ++ ys))) (unflatten ((xs₁ ++ xs₂) ++ ys))
      s-id⁻ = subst (λ z → HomTerm (unflatten z) (unflatten ((xs₁ ++ xs₂) ++ ys))) e id

      Lhs    = α⇒ {U₁} {U₂} {Uys} ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys
      Rhs    = (id {U₁} ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id
      Lhsinv = to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐ {U₁} {U₂} {Uys}
      Rhsinv = s-id⁻ ∘ to₁₂₃ ∘ (id {U₁} ⊗₁ to₂₃)

      -- `s-id⁻ ∘ s-id ≈ id` (subst of `e` after `e`; refl-case is `id ∘ id`).
      s-id⁻-s-id : s-id⁻ ∘ s-id ≈Term id
      s-id⁻-s-id = lemma e
        where
          lemma : ∀ {a b : List X} (p : a ≡ b)
                → subst (λ z → HomTerm (unflatten z) (unflatten a)) p id
                  ∘ subst (λ z → HomTerm (unflatten a) (unflatten z)) p id
                  ≈Term id
          lemma refl = idˡ

      LhsLhsinv : Lhs ∘ Lhsinv ≈Term id
      LhsLhsinv = begin
        (α⇒ ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys) ∘ (to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐)
          ≈⟨ FM.assoc ⟩
        α⇒ ∘ ((from₁₂ ⊗₁ id) ∘ from₁₂ys) ∘ (to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        α⇒ ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys ∘ to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        α⇒ ∘ (from₁₂ ⊗₁ id) ∘ (from₁₂ys ∘ to₁₂ys) ∘ (to₁₂ ⊗₁ id) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (unflatten-++-≅ (xs₁ ++ xs₂) ys) ⟩∘⟨refl ⟩
        α⇒ ∘ (from₁₂ ⊗₁ id) ∘ id ∘ (to₁₂ ⊗₁ id) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        α⇒ ∘ (from₁₂ ⊗₁ id) ∘ (to₁₂ ⊗₁ id) ∘ α⇐
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        α⇒ ∘ ((from₁₂ ⊗₁ id) ∘ (to₁₂ ⊗₁ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
        α⇒ ∘ ((from₁₂ ∘ to₁₂) ⊗₁ (id ∘ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-++-≅ xs₁ xs₂)) idˡ ⟩∘⟨refl ⟩
        α⇒ ∘ (id ⊗₁ id) ∘ α⇐
          ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
        α⇒ ∘ id ∘ α⇐
          ≈⟨ refl⟩∘⟨ idˡ ⟩
        α⇒ ∘ α⇐
          ≈⟨ α⇒∘α⇐≈id ⟩
        id ∎

      RhsinvRhs : Rhsinv ∘ Rhs ≈Term id
      RhsinvRhs = begin
        (s-id⁻ ∘ to₁₂₃ ∘ (id ⊗₁ to₂₃)) ∘ ((id ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id)
          ≈⟨ FM.assoc ⟩
        s-id⁻ ∘ (to₁₂₃ ∘ (id ⊗₁ to₂₃)) ∘ ((id ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        s-id⁻ ∘ to₁₂₃ ∘ (id ⊗₁ to₂₃) ∘ (id ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        s-id⁻ ∘ to₁₂₃ ∘ ((id ⊗₁ to₂₃) ∘ (id ⊗₁ from₂₃)) ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
        s-id⁻ ∘ to₁₂₃ ∘ ((id ∘ id) ⊗₁ (to₂₃ ∘ from₂₃)) ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ xs₂ ys)) ⟩∘⟨refl ⟩
        s-id⁻ ∘ to₁₂₃ ∘ (id ⊗₁ id) ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
        s-id⁻ ∘ to₁₂₃ ∘ id ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        s-id⁻ ∘ to₁₂₃ ∘ from₁₂₃ ∘ s-id
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        s-id⁻ ∘ (to₁₂₃ ∘ from₁₂₃) ∘ s-id
          ≈⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-++-≅ xs₁ (xs₂ ++ ys)) ⟩∘⟨refl ⟩
        s-id⁻ ∘ id ∘ s-id
          ≈⟨ refl⟩∘⟨ idˡ ⟩
        s-id⁻ ∘ s-id
          ≈⟨ s-id⁻-s-id ⟩
        id ∎

  ------------------------------------------------------------------------
  -- `subst₂ HomTerm (cong unflatten p) (cong unflatten q) t` as a
  -- conjugation by `subst`-identity morphisms.
  subst-id-dom : ∀ {a b : List X} → a ≡ b
               → HomTerm (unflatten b) (unflatten a)
  subst-id-dom {a} p = subst (λ z → HomTerm (unflatten z) (unflatten a)) p id

  subst-id-cod : ∀ {c d : List X} → c ≡ d
               → HomTerm (unflatten c) (unflatten d)
  subst-id-cod {c} q = subst (λ z → HomTerm (unflatten c) (unflatten z)) q id

  ------------------------------------------------------------------------
  -- Shared associativity re-bracketing for `box-suffix` / `box-prefix`'s
  -- `regroup-L` step: a `T ∘ (A ∘ (αc ∘ X ∘ ac) ∘ B) ∘ F` composite, with an
  -- `αc ∘ X ∘ ac` core inside, re-brackets into the three target blocks
  -- `(T ∘ A ∘ αc) ∘ X ∘ (ac ∘ B ∘ F)`.  Pure associativity (no use of the
  -- `α`/`⊗` structure of the arguments), so it is fully generic.
  bracket-αXα
    : ∀ {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ : ObjTerm}
        (T : HomTerm O₆ O₇) (A : HomTerm O₅ O₆) (αc : HomTerm O₄ O₅)
        (X : HomTerm O₃ O₄) (ac : HomTerm O₂ O₃)
        (B : HomTerm O₁ O₂) (F : HomTerm O₀ O₁)
    → T ∘ (A ∘ (αc ∘ X ∘ ac) ∘ B) ∘ F
      ≈Term (T ∘ A ∘ αc) ∘ X ∘ ac ∘ B ∘ F
  bracket-αXα T A αc X ac B F = begin
      T ∘ (A ∘ (αc ∘ X ∘ ac) ∘ B) ∘ F
        ≈⟨ FM.sym-assoc ⟩
      (T ∘ (A ∘ (αc ∘ X ∘ ac) ∘ B)) ∘ F
        ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
      ((T ∘ A) ∘ (αc ∘ X ∘ ac) ∘ B) ∘ F
        ≈⟨ FM.assoc ⟩
      (T ∘ A) ∘ ((αc ∘ X ∘ ac) ∘ B) ∘ F
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      (T ∘ A) ∘ (αc ∘ X ∘ ac) ∘ B ∘ F
        ≈⟨ FM.sym-assoc ⟩
      ((T ∘ A) ∘ (αc ∘ X ∘ ac)) ∘ B ∘ F
        ≈⟨ FM.assoc ⟩∘⟨refl ⟩
      (T ∘ A ∘ (αc ∘ X ∘ ac)) ∘ B ∘ F
        ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
      (T ∘ (A ∘ αc) ∘ (X ∘ ac)) ∘ B ∘ F
        ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
      (T ∘ ((A ∘ αc) ∘ X) ∘ ac) ∘ B ∘ F
        ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
      ((T ∘ ((A ∘ αc) ∘ X)) ∘ ac) ∘ B ∘ F
        ≈⟨ (FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (((T ∘ (A ∘ αc)) ∘ X) ∘ ac) ∘ B ∘ F
        ≈⟨ ((FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((((T ∘ A) ∘ αc) ∘ X) ∘ ac) ∘ B ∘ F
        ≈⟨ ((FM.assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (((T ∘ A ∘ αc) ∘ X) ∘ ac) ∘ B ∘ F
        ≈⟨ FM.assoc ⟩∘⟨refl ⟩
      ((T ∘ A ∘ αc) ∘ (X ∘ ac)) ∘ B ∘ F
        ≈⟨ FM.assoc ⟩
      (T ∘ A ∘ αc) ∘ (X ∘ ac) ∘ B ∘ F
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      (T ∘ A ∘ αc) ∘ X ∘ ac ∘ B ∘ F ∎

  ------------------------------------------------------------------------
  -- BOX-SUFFIX: a box on residual `restG ++ R` factors (modulo the
  -- `++-assoc` boundary transport) as `(box on restG) ⊗₁ id` framed by
  -- `unflatten-++-≅ (·++restG) R`.
  box-suffix
    : ∀ (einL eoutL restG R : List X) (g : FlatGen einL eoutL)
    → subst₂ HomTerm
        (cong unflatten (sym (++-assoc einL  restG R)))
        (cong unflatten (sym (++-assoc eoutL restG R)))
        (box-of einL eoutL (restG ++ R) g)
      ≈Term _≅_.to (unflatten-++-≅ (eoutL ++ restG) R)
            ∘ (box-of einL eoutL restG g ⊗₁ id {unflatten R})
            ∘ _≅_.from (unflatten-++-≅ (einL ++ restG) R)
  box-suffix einL eoutL restG R g = goal
    where
      G   = Agen-edge-aux g
      UR  = unflatten R
      Ueo = unflatten eoutL
      Uei = unflatten einL
      Urg = unflatten restG

      -- raw box on the `restG ++ R` residual.
      to-eo-rgR   = _≅_.to   (unflatten-++-≅ eoutL (restG ++ R))
      from-ei-rgR = _≅_.from (unflatten-++-≅ einL  (restG ++ R))
      bxRaw = to-eo-rgR ∘ (G ⊗₁ id {unflatten (restG ++ R)}) ∘ from-ei-rgR

      -- box on `restG` (the `bx` of the RHS).
      to-eo-rg   = _≅_.to   (unflatten-++-≅ eoutL restG)
      from-ei-rg = _≅_.from (unflatten-++-≅ einL  restG)
      bx = to-eo-rg ∘ (G ⊗₁ id {Urg}) ∘ from-ei-rg

      to-eorg-R   = _≅_.to   (unflatten-++-≅ (eoutL ++ restG) R)
      from-eirg-R = _≅_.from (unflatten-++-≅ (einL ++ restG) R)

      from-rgR = _≅_.from (unflatten-++-≅ restG R)
      to-rgR   = _≅_.to   (unflatten-++-≅ restG R)

      -- the `subst`-id bridge morphisms produced by c-iso-assoc-from/to.
      s-ei : HomTerm (unflatten ((einL ++ restG) ++ R)) (unflatten (einL ++ (restG ++ R)))
      s-ei = subst (λ z → HomTerm (unflatten ((einL ++ restG) ++ R)) (unflatten z))
                   (++-assoc einL restG R) id
      s-eo⁻ : HomTerm (unflatten (eoutL ++ (restG ++ R))) (unflatten ((eoutL ++ restG) ++ R))
      s-eo⁻ = subst (λ z → HomTerm (unflatten z) (unflatten ((eoutL ++ restG) ++ R)))
                    (++-assoc eoutL restG R) id

      -- the LHS `subst₂` as the conjugation `s-eo⁻ ∘ bxRaw ∘ s-ei`.
      -- `conj-lemma` produces conjugating morphisms along `sym p`/`sym q`;
      -- instantiated at `p = sym (++-assoc …)` these are exactly `s-ei`/`s-eo⁻`
      -- after `sym²`.
      conj-lemma
        : ∀ {A B A' B' : ObjTerm} (p : A ≡ A') (q : B ≡ B') (t : HomTerm A B)
        → subst₂ HomTerm p q t
          ≈Term subst (λ z → HomTerm B z) q id
                ∘ t
                ∘ subst (λ z → HomTerm z A) p id
      conj-lemma refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)

      -- The c-iso-assoc `s-ei`/`s-eo⁻` re-expressed as `subst` over the
      -- raw `HomTerm` arguments (matching `conj-lemma`'s conjugators).
      s-ei-as : subst (λ z → HomTerm z (unflatten (einL ++ (restG ++ R))))
                      (cong unflatten (sym (++-assoc einL restG R))) id
              ≡ s-ei
      s-ei-as = bridge (++-assoc einL restG R)
        where
          bridge : ∀ {a b : List X} (e : a ≡ b)
                 → subst (λ z → HomTerm z (unflatten b)) (cong unflatten (sym e)) id
                   ≡ subst (λ z → HomTerm (unflatten a) (unflatten z)) e id
          bridge refl = refl

      s-eo⁻-as : subst (λ z → HomTerm (unflatten (eoutL ++ (restG ++ R))) z)
                       (cong unflatten (sym (++-assoc eoutL restG R))) id
               ≡ s-eo⁻
      s-eo⁻-as = bridge (++-assoc eoutL restG R)
        where
          bridge : ∀ {a b : List X} (e : a ≡ b)
                 → subst (λ z → HomTerm (unflatten b) z) (cong unflatten (sym e)) id
                   ≡ subst (λ z → HomTerm (unflatten z) (unflatten a)) e id
          bridge refl = refl

      lhs-conj :
        subst₂ HomTerm
          (cong unflatten (sym (++-assoc einL  restG R)))
          (cong unflatten (sym (++-assoc eoutL restG R)))
          bxRaw
        ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
      lhs-conj =
        ≈-Term-trans
          (conj-lemma (cong unflatten (sym (++-assoc einL restG R)))
                      (cong unflatten (sym (++-assoc eoutL restG R))) bxRaw)
          (∘-resp-≈ (≡⇒≈Term s-eo⁻-as)
            (∘-resp-≈ ≈-Term-refl (≡⇒≈Term s-ei-as)))

      goal :
        subst₂ HomTerm
          (cong unflatten (sym (++-assoc einL  restG R)))
          (cong unflatten (sym (++-assoc eoutL restG R)))
          bxRaw
        ≈Term to-eorg-R ∘ (bx ⊗₁ id {UR}) ∘ from-eirg-R
      goal = ≈-Term-trans lhs-conj (≈-Term-sym rhs-chase)
        where
          -- F-ei : `α⇒ ∘ (from-ei-rg ⊗₁ id) ∘ from-eirg-R
          --          ≈ (id ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei`.
          F-ei = c-iso-assoc-from einL restG R
          -- T-eo : `to-eorg-R ∘ (to-eo-rg ⊗₁ id) ∘ α⇐
          --          ≈ s-eo⁻ ∘ to-eo-rgR ∘ (id ⊗₁ to-rgR)`.
          T-eo = c-iso-assoc-to eoutL restG R

          -- the middle bifunctor collapse:
          --   (id ⊗₁ to-rgR) ∘ (G ⊗₁ id_{Urg⊗UR}) ∘ (id ⊗₁ from-rgR)
          --     ≈ G ⊗₁ id_{U(restG++R)}.
          mid-collapse
            : (id {Ueo} ⊗₁ to-rgR) ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ (id {Uei} ⊗₁ from-rgR)
              ≈Term G ⊗₁ id {unflatten (restG ++ R)}
          mid-collapse = begin
            (id ⊗₁ to-rgR) ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ (id ⊗₁ from-rgR)
              ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (id ⊗₁ to-rgR) ∘ ((G ∘ id) ⊗₁ (id {Urg ⊗₀ UR} ∘ from-rgR))
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idʳ idˡ ⟩
            (id ⊗₁ to-rgR) ∘ (G ⊗₁ from-rgR)
              ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (id ∘ G) ⊗₁ (to-rgR ∘ from-rgR)
              ≈⟨ ⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ restG R)) ⟩
            G ⊗₁ id {unflatten (restG ++ R)} ∎

          -- ⊗-functoriality: `bx ⊗₁ id` distributes over `bx`'s three
          -- factors (the `mid-collapse`-style `⊗-∘-dist` expansion).
          bx⊗id-expand
            : (bx ⊗₁ id {UR})
              ≈Term (to-eo-rg ⊗₁ id {UR})
                    ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
                    ∘ (from-ei-rg ⊗₁ id {UR})
          bx⊗id-expand = begin
            bx ⊗₁ id {UR}
              ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym (≈-Term-trans idˡ idˡ)) ⟩
            (to-eo-rg ∘ (G ⊗₁ id {Urg}) ∘ from-ei-rg) ⊗₁ (id ∘ id ∘ id)
              ≈⟨ ⊗-∘-dist ⟩
            (to-eo-rg ⊗₁ id {UR})
              ∘ (((G ⊗₁ id {Urg}) ∘ from-ei-rg) ⊗₁ (id ∘ id))
              ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
            (to-eo-rg ⊗₁ id {UR})
              ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
              ∘ (from-ei-rg ⊗₁ id {UR}) ∎

          -- associator naturality (the `α-comm` instance, f = G, g/h = id):
          --   `(G ⊗ id_{Urg}) ⊗ id_{UR} ≈ α⇐ ∘ (G ⊗ id_{Urg⊗UR}) ∘ α⇒`.
          mid-nat
            : ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
              ≈Term α⇐ {Ueo} {Urg} {UR}
                    ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                    ∘ α⇒ {Uei} {Urg} {UR}
          mid-nat = begin
            (G ⊗₁ id {Urg}) ⊗₁ id {UR}
              ≈⟨ ≈-Term-sym idˡ ⟩
            id ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
              ≈⟨ ≈-Term-sym α⇐∘α⇒≈id ⟩∘⟨refl ⟩
            (α⇐ {Ueo} {Urg} {UR} ∘ α⇒ {Ueo} {Urg} {UR})
              ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
              ≈⟨ FM.assoc ⟩
            α⇐ {Ueo} {Urg} {UR}
              ∘ (α⇒ {Ueo} {Urg} {UR} ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR}))
              ≈⟨ refl⟩∘⟨ α-comm ⟩
            α⇐ {Ueo} {Urg} {UR}
              ∘ ((G ⊗₁ (id {Urg} ⊗₁ id {UR})) ∘ α⇒ {Uei} {Urg} {UR})
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩∘⟨refl ⟩
            α⇐ {Ueo} {Urg} {UR}
              ∘ (G ⊗₁ id {Urg ⊗₀ UR})
              ∘ α⇒ {Uei} {Urg} {UR} ∎

          rhs-chase
            : to-eorg-R ∘ (bx ⊗₁ id {UR}) ∘ from-eirg-R
              ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
          rhs-chase = begin
            to-eorg-R ∘ (bx ⊗₁ id {UR}) ∘ from-eirg-R
              -- Step 1: ⊗-functoriality.
              ≈⟨ refl⟩∘⟨ bx⊗id-expand ⟩∘⟨refl ⟩
            to-eorg-R
              ∘ ((to-eo-rg ⊗₁ id {UR})
                 ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
                 ∘ (from-ei-rg ⊗₁ id {UR}))
              ∘ from-eirg-R
              -- Step 2: associator naturality on the middle factor.
              ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ mid-nat ⟩∘⟨refl) ⟩∘⟨refl ⟩
            to-eorg-R
              ∘ ((to-eo-rg ⊗₁ id {UR})
                 ∘ (α⇐ {Ueo} {Urg} {UR}
                    ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                    ∘ α⇒ {Uei} {Urg} {UR})
                 ∘ (from-ei-rg ⊗₁ id {UR}))
              ∘ from-eirg-R
              -- Step 3a: regroup into the three T-eo / mid / F-ei blocks.
              ≈⟨ regroup-L ⟩
            (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
              ∘ (G ⊗₁ id {Urg ⊗₀ UR})
              ∘ (α⇒ {Uei} {Urg} {UR}
                 ∘ (from-ei-rg ⊗₁ id {UR})
                 ∘ from-eirg-R)
              -- Step 3b: apply T-eo (left block) and F-ei (right block).
              ≈⟨ T-eo ⟩∘⟨ refl⟩∘⟨ F-ei ⟩
            (s-eo⁻ ∘ to-eo-rgR ∘ (id {Ueo} ⊗₁ to-rgR))
              ∘ (G ⊗₁ id {Urg ⊗₀ UR})
              ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
              -- Step 4a: regroup to expose the mid-collapse triple.
              ≈⟨ regroup-mid ⟩
            s-eo⁻
              ∘ to-eo-rgR
              ∘ ((id {Ueo} ⊗₁ to-rgR)
                 ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                 ∘ (id {Uei} ⊗₁ from-rgR))
              ∘ from-ei-rgR
              ∘ s-ei
              -- Step 4b: mid-collapse.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-collapse ⟩∘⟨refl ⟩
            s-eo⁻
              ∘ to-eo-rgR
              ∘ (G ⊗₁ id {unflatten (restG ++ R)})
              ∘ from-ei-rgR
              ∘ s-ei
              -- Step 5: regroup `to-eo-rgR ∘ (G ⊗ id) ∘ from-ei-rgR = bxRaw`.
              ≈⟨ regroup-R ⟩
            s-eo⁻ ∘ bxRaw ∘ s-ei ∎
            where
              -- The three pure-associativity reshuffles.
              regroup-L :
                to-eorg-R
                  ∘ ((to-eo-rg ⊗₁ id {UR})
                     ∘ (α⇐ {Ueo} {Urg} {UR}
                        ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                        ∘ α⇒ {Uei} {Urg} {UR})
                     ∘ (from-ei-rg ⊗₁ id {UR}))
                  ∘ from-eirg-R
                ≈Term
                (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ (α⇒ {Uei} {Urg} {UR}
                     ∘ (from-ei-rg ⊗₁ id {UR})
                     ∘ from-eirg-R)
              regroup-L =
                bracket-αXα to-eorg-R (to-eo-rg ⊗₁ id {UR}) (α⇐ {Ueo} {Urg} {UR})
                  (G ⊗₁ id {Urg ⊗₀ UR}) (α⇒ {Uei} {Urg} {UR})
                  (from-ei-rg ⊗₁ id {UR}) from-eirg-R

              regroup-mid :
                (s-eo⁻ ∘ to-eo-rgR ∘ (id {Ueo} ⊗₁ to-rgR))
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
                ≈Term
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ ((id {Ueo} ⊗₁ to-rgR)
                     ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                     ∘ (id {Uei} ⊗₁ from-rgR))
                  ∘ from-ei-rgR
                  ∘ s-ei
              regroup-mid = begin
                (s-eo⁻ ∘ to-eo-rgR ∘ (id {Ueo} ⊗₁ to-rgR))
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
                  -- S → FRA: peel `s-eo⁻`, then `to-eo-rgR`, off the front.
                  ≈⟨ FM.assoc ⟩
                s-eo⁻
                  ∘ (to-eo-rgR ∘ (id {Ueo} ⊗₁ to-rgR))
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ (id {Ueo} ⊗₁ to-rgR)
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
                  -- FRA → G: group `T₁ ∘ M`, then `(T₁∘M) ∘ B₁`, then
                  --   re-associate to `(T₁ ∘ M ∘ B₁)`.
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ ((id {Ueo} ⊗₁ to-rgR) ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                  ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ (((id {Ueo} ⊗₁ to-rgR) ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                     ∘ (id {Uei} ⊗₁ from-rgR))
                  ∘ (from-ei-rgR ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ ((id {Ueo} ⊗₁ to-rgR)
                     ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                     ∘ (id {Uei} ⊗₁ from-rgR))
                  ∘ (from-ei-rgR ∘ s-ei) ∎

              regroup-R :
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ (G ⊗₁ id {unflatten (restG ++ R)})
                  ∘ from-ei-rgR
                  ∘ s-ei
                ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
              regroup-R = begin
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ (G ⊗₁ id {unflatten (restG ++ R)})
                  ∘ from-ei-rgR
                  ∘ s-ei
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ ((G ⊗₁ id {unflatten (restG ++ R)}) ∘ from-ei-rgR)
                  ∘ s-ei
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻ ∘ bxRaw ∘ s-ei ∎

  ------------------------------------------------------------------------
  -- BOX-PREFIX: the mirror image of `box-suffix`.  A box whose generator
  -- acts on the right block `einR→eoutR` but is preceded by an UNTOUCHED
  -- left prefix `P` (a "P-prefixed box"), running on residual `restK`,
  -- factors — modulo the `++-assoc` boundary transport — as the same
  -- P-prefixed box on the EMPTY residual, tensored with `id` on the
  -- untouched far suffix `restK`, framed by `unflatten-++-≅ (P++·) restK`.
  --
  --   Pbox restK ≈ subst₂ … (to(uf++ (P++eoutR) restK)
  --                            ∘ (Pbox-empty ⊗₁ id {U restK})
  --                            ∘ from(uf++ (P++einR) restK))
  --
  -- where  Pbox M     = to(uf++ P (eoutR++M)) ∘ (id_{U P} ⊗₁ box-of einR eoutR M g)
  --                       ∘ from(uf++ P (einR++M))
  --   and  Pbox-empty = to(uf++ P eoutR) ∘ (id_{U P} ⊗₁ Agen) ∘ from(uf++ P einR).
  --
  -- Same proof shape as `box-suffix` (⊗-functoriality expand + α-comm +
  -- c-iso-assoc-from/to at lists `(P, einR, restK)` + bifunctor
  -- mid-collapse), with the box generator on the RIGHT factor.
  box-prefix
    : ∀ (P einR eoutR restK : List X) (g : FlatGen einR eoutR)
    → subst₂ HomTerm
        (cong unflatten (sym (++-assoc P einR  restK)))
        (cong unflatten (sym (++-assoc P eoutR restK)))
        (_≅_.to (unflatten-++-≅ P (eoutR ++ restK))
         ∘ (id {unflatten P} ⊗₁ box-of einR eoutR restK g)
         ∘ _≅_.from (unflatten-++-≅ P (einR ++ restK)))
      ≈Term _≅_.to (unflatten-++-≅ (P ++ eoutR) restK)
            ∘ ((_≅_.to (unflatten-++-≅ P eoutR)
                ∘ (id {unflatten P} ⊗₁ Agen-edge-aux g)
                ∘ _≅_.from (unflatten-++-≅ P einR)) ⊗₁ id {unflatten restK})
            ∘ _≅_.from (unflatten-++-≅ (P ++ einR) restK)
  box-prefix P einR eoutR restK g = goal
    where
      G   = Agen-edge-aux g
      UP  = unflatten P
      Uei = unflatten einR
      Ueo = unflatten eoutR
      Urk = unflatten restK

      -- box-of `einR` with residual `restK` (the inner factor of `Pbox`).
      to-eo-rk   = _≅_.to   (unflatten-++-≅ eoutR restK)
      from-ei-rk = _≅_.from (unflatten-++-≅ einR  restK)
      bx = to-eo-rk ∘ (G ⊗₁ id {Urk}) ∘ from-ei-rk

      -- `Pbox restK` (the LHS box, with the `id_{UP} ⊗ box-of …` middle).
      to-P-eork   = _≅_.to   (unflatten-++-≅ P (eoutR ++ restK))
      from-P-eirk = _≅_.from (unflatten-++-≅ P (einR  ++ restK))
      bxRaw = to-P-eork ∘ (id {UP} ⊗₁ bx) ∘ from-P-eirk

      -- The `(P++einR/eoutR)`-grouped framing of the RHS.
      to-Peo-rk   = _≅_.to   (unflatten-++-≅ (P ++ eoutR) restK)
      from-Pei-rk = _≅_.from (unflatten-++-≅ (P ++ einR)  restK)

      -- P-prefixed box on the EMPTY residual (the RHS `bx'`).
      to-P-eo   = _≅_.to   (unflatten-++-≅ P eoutR)
      from-P-ei = _≅_.from (unflatten-++-≅ P einR)
      bx' = to-P-eo ∘ (id {UP} ⊗₁ G) ∘ from-P-ei

      -- the `subst`-id bridges produced by c-iso-assoc-from/to.
      s-ei : HomTerm (unflatten ((P ++ einR) ++ restK)) (unflatten (P ++ (einR ++ restK)))
      s-ei = subst (λ z → HomTerm (unflatten ((P ++ einR) ++ restK)) (unflatten z))
                   (++-assoc P einR restK) id
      s-eo⁻ : HomTerm (unflatten (P ++ (eoutR ++ restK))) (unflatten ((P ++ eoutR) ++ restK))
      s-eo⁻ = subst (λ z → HomTerm (unflatten z) (unflatten ((P ++ eoutR) ++ restK)))
                    (++-assoc P eoutR restK) id

      conj-lemma
        : ∀ {A B A' B' : ObjTerm} (p : A ≡ A') (q : B ≡ B') (t : HomTerm A B)
        → subst₂ HomTerm p q t
          ≈Term subst (λ z → HomTerm B z) q id
                ∘ t
                ∘ subst (λ z → HomTerm z A) p id
      conj-lemma refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)

      s-ei-as : subst (λ z → HomTerm z (unflatten (P ++ (einR ++ restK))))
                      (cong unflatten (sym (++-assoc P einR restK))) id
              ≡ s-ei
      s-ei-as = bridge (++-assoc P einR restK)
        where
          bridge : ∀ {a b : List X} (e : a ≡ b)
                 → subst (λ z → HomTerm z (unflatten b)) (cong unflatten (sym e)) id
                   ≡ subst (λ z → HomTerm (unflatten a) (unflatten z)) e id
          bridge refl = refl

      s-eo⁻-as : subst (λ z → HomTerm (unflatten (P ++ (eoutR ++ restK))) z)
                       (cong unflatten (sym (++-assoc P eoutR restK))) id
               ≡ s-eo⁻
      s-eo⁻-as = bridge (++-assoc P eoutR restK)
        where
          bridge : ∀ {a b : List X} (e : a ≡ b)
                 → subst (λ z → HomTerm (unflatten b) z) (cong unflatten (sym e)) id
                   ≡ subst (λ z → HomTerm (unflatten z) (unflatten a)) e id
          bridge refl = refl

      lhs-conj :
        subst₂ HomTerm
          (cong unflatten (sym (++-assoc P einR  restK)))
          (cong unflatten (sym (++-assoc P eoutR restK)))
          bxRaw
        ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
      lhs-conj =
        ≈-Term-trans
          (conj-lemma (cong unflatten (sym (++-assoc P einR restK)))
                      (cong unflatten (sym (++-assoc P eoutR restK))) bxRaw)
          (∘-resp-≈ (≡⇒≈Term s-eo⁻-as)
            (∘-resp-≈ ≈-Term-refl (≡⇒≈Term s-ei-as)))

      goal :
        subst₂ HomTerm
          (cong unflatten (sym (++-assoc P einR  restK)))
          (cong unflatten (sym (++-assoc P eoutR restK)))
          bxRaw
        ≈Term to-Peo-rk ∘ (bx' ⊗₁ id {Urk}) ∘ from-Pei-rk
      goal = ≈-Term-trans lhs-conj (≈-Term-sym rhs-chase)
        where
          F-ei = c-iso-assoc-from P einR restK
          T-eo = c-iso-assoc-to P eoutR restK

          -- the middle bifunctor collapse (generator on the right factor):
          --   (id_UP ⊗ to-eo-rk) ∘ (id_UP ⊗ (G⊗id)) ∘ (id_UP ⊗ from-ei-rk)
          --     ≈ id_UP ⊗ bx.
          mid-collapse
            : (id {UP} ⊗₁ to-eo-rk)
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ (id {UP} ⊗₁ from-ei-rk)
              ≈Term id {UP} ⊗₁ bx
          mid-collapse = begin
            (id {UP} ⊗₁ to-eo-rk)
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ (id {UP} ⊗₁ from-ei-rk)
              ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (id {UP} ⊗₁ to-eo-rk)
              ∘ ((id ∘ id) ⊗₁ ((G ⊗₁ id {Urk}) ∘ from-ei-rk))
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
            (id {UP} ⊗₁ to-eo-rk)
              ∘ (id ⊗₁ ((G ⊗₁ id {Urk}) ∘ from-ei-rk))
              ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (id ∘ id) ⊗₁ (to-eo-rk ∘ (G ⊗₁ id {Urk}) ∘ from-ei-rk)
              ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
            id {UP} ⊗₁ bx ∎

          -- ⊗-functoriality: `bx' ⊗ id` distributes over bx''s three factors.
          bx'⊗id-expand
            : (bx' ⊗₁ id {Urk})
              ≈Term (to-P-eo ⊗₁ id {Urk})
                    ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
                    ∘ (from-P-ei ⊗₁ id {Urk})
          bx'⊗id-expand = begin
            bx' ⊗₁ id {Urk}
              ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym (≈-Term-trans idˡ idˡ)) ⟩
            (to-P-eo ∘ (id {UP} ⊗₁ G) ∘ from-P-ei) ⊗₁ (id ∘ id ∘ id)
              ≈⟨ ⊗-∘-dist ⟩
            (to-P-eo ⊗₁ id {Urk})
              ∘ (((id {UP} ⊗₁ G) ∘ from-P-ei) ⊗₁ (id ∘ id))
              ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
            (to-P-eo ⊗₁ id {Urk})
              ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
              ∘ (from-P-ei ⊗₁ id {Urk}) ∎

          -- associator naturality (the `α-comm` instance, on the left
          -- prefix `id {UP}` past the box middle):
          --   `(id_UP ⊗ G) ⊗ id_Urk ≈ α⇐ ∘ (id_UP ⊗ (G⊗id)) ∘ α⇒`.
          mid-nat
            : ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
              ≈Term α⇐ {UP} {Ueo} {Urk}
                    ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                    ∘ α⇒ {UP} {Uei} {Urk}
          mid-nat = begin
            (id {UP} ⊗₁ G) ⊗₁ id {Urk}
              ≈⟨ ≈-Term-sym idˡ ⟩
            id ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
              ≈⟨ ≈-Term-sym α⇐∘α⇒≈id ⟩∘⟨refl ⟩
            (α⇐ {UP} {Ueo} {Urk} ∘ α⇒ {UP} {Ueo} {Urk})
              ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
              ≈⟨ FM.assoc ⟩
            α⇐ {UP} {Ueo} {Urk}
              ∘ (α⇒ {UP} {Ueo} {Urk} ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk}))
              ≈⟨ refl⟩∘⟨ α-comm ⟩
            α⇐ {UP} {Ueo} {Urk}
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ α⇒ {UP} {Uei} {Urk} ∎

          rhs-chase
            : to-Peo-rk ∘ (bx' ⊗₁ id {Urk}) ∘ from-Pei-rk
              ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
          rhs-chase = begin
            to-Peo-rk ∘ (bx' ⊗₁ id {Urk}) ∘ from-Pei-rk
              -- Step 1: ⊗-functoriality.
              ≈⟨ refl⟩∘⟨ bx'⊗id-expand ⟩∘⟨refl ⟩
            to-Peo-rk
              ∘ ((to-P-eo ⊗₁ id {Urk})
                 ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
                 ∘ (from-P-ei ⊗₁ id {Urk}))
              ∘ from-Pei-rk
              -- Step 2: associator naturality on the middle factor.
              ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ mid-nat ⟩∘⟨refl) ⟩∘⟨refl ⟩
            to-Peo-rk
              ∘ ((to-P-eo ⊗₁ id {Urk})
                 ∘ (α⇐ {UP} {Ueo} {Urk}
                    ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                    ∘ α⇒ {UP} {Uei} {Urk})
                 ∘ (from-P-ei ⊗₁ id {Urk}))
              ∘ from-Pei-rk
              -- Step 3a: regroup into the three T-eo / mid / F-ei blocks.
              ≈⟨ regroup-L ⟩
            (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ (α⇒ {UP} {Uei} {Urk}
                 ∘ (from-P-ei ⊗₁ id {Urk})
                 ∘ from-Pei-rk)
              -- Step 3b: apply T-eo (left block) and F-ei (right block).
              ≈⟨ T-eo ⟩∘⟨ refl⟩∘⟨ F-ei ⟩
            (s-eo⁻ ∘ to-P-eork ∘ (id {UP} ⊗₁ to-eo-rk))
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
              -- Step 4a: regroup to expose the mid-collapse triple.
              ≈⟨ regroup-mid ⟩
            s-eo⁻
              ∘ to-P-eork
              ∘ ((id {UP} ⊗₁ to-eo-rk)
                 ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                 ∘ (id {UP} ⊗₁ from-ei-rk))
              ∘ from-P-eirk
              ∘ s-ei
              -- Step 4b: mid-collapse.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-collapse ⟩∘⟨refl ⟩
            s-eo⁻
              ∘ to-P-eork
              ∘ (id {UP} ⊗₁ bx)
              ∘ from-P-eirk
              ∘ s-ei
              -- Step 5: regroup `to-P-eork ∘ (id ⊗ bx) ∘ from-P-eirk = bxRaw`.
              ≈⟨ regroup-R ⟩
            s-eo⁻ ∘ bxRaw ∘ s-ei ∎
            where
              regroup-L :
                to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk})
                     ∘ (α⇐ {UP} {Ueo} {Urk}
                        ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                        ∘ α⇒ {UP} {Uei} {Urk})
                     ∘ (from-P-ei ⊗₁ id {Urk}))
                  ∘ from-Pei-rk
                ≈Term
                (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ (α⇒ {UP} {Uei} {Urk}
                     ∘ (from-P-ei ⊗₁ id {Urk})
                     ∘ from-Pei-rk)
              regroup-L =
                bracket-αXα to-Peo-rk (to-P-eo ⊗₁ id {Urk}) (α⇐ {UP} {Ueo} {Urk})
                  (id {UP} ⊗₁ (G ⊗₁ id {Urk})) (α⇒ {UP} {Uei} {Urk})
                  (from-P-ei ⊗₁ id {Urk}) from-Pei-rk

              regroup-mid :
                (s-eo⁻ ∘ to-P-eork ∘ (id {UP} ⊗₁ to-eo-rk))
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
                ≈Term
                s-eo⁻
                  ∘ to-P-eork
                  ∘ ((id {UP} ⊗₁ to-eo-rk)
                     ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                     ∘ (id {UP} ⊗₁ from-ei-rk))
                  ∘ from-P-eirk
                  ∘ s-ei
              regroup-mid = begin
                (s-eo⁻ ∘ to-P-eork ∘ (id {UP} ⊗₁ to-eo-rk))
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
                  ≈⟨ FM.assoc ⟩
                s-eo⁻
                  ∘ (to-P-eork ∘ (id {UP} ⊗₁ to-eo-rk))
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                s-eo⁻
                  ∘ to-P-eork
                  ∘ (id {UP} ⊗₁ to-eo-rk)
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-P-eork
                  ∘ ((id {UP} ⊗₁ to-eo-rk) ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                  ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-P-eork
                  ∘ (((id {UP} ⊗₁ to-eo-rk) ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                     ∘ (id {UP} ⊗₁ from-ei-rk))
                  ∘ (from-P-eirk ∘ s-ei)
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
                s-eo⁻
                  ∘ to-P-eork
                  ∘ ((id {UP} ⊗₁ to-eo-rk)
                     ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                     ∘ (id {UP} ⊗₁ from-ei-rk))
                  ∘ (from-P-eirk ∘ s-ei) ∎

              regroup-R :
                s-eo⁻
                  ∘ to-P-eork
                  ∘ (id {UP} ⊗₁ bx)
                  ∘ from-P-eirk
                  ∘ s-ei
                ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
              regroup-R = begin
                s-eo⁻
                  ∘ to-P-eork
                  ∘ (id {UP} ⊗₁ bx)
                  ∘ from-P-eirk
                  ∘ s-ei
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻
                  ∘ to-P-eork
                  ∘ ((id {UP} ⊗₁ bx) ∘ from-P-eirk)
                  ∘ s-ei
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                s-eo⁻ ∘ bxRaw ∘ s-ei ∎

  ------------------------------------------------------------------------
  -- BOX-BRAID: the σ-mirror of `box-suffix`.  A FRONT-acting box on the
  -- residual `P ++ rest` factors as the SAME box held AFTER the prefix
  -- `P` (i.e. `id {unflatten P} ⊗₁ box-of einR eoutR rest g`), conjugated
  -- by the block-swap braids `σ-in`/`σ-out` that move the `einR`/`eoutR`
  -- front-block past `P` (carrying `rest`).
  --
  --   box-of einR eoutR (P ++ rest) g
  --     ≈ σ-out ∘ (id {unflatten P} ⊗₁ box-of einR eoutR rest g) ∘ σ-in
  --
  -- where (with Uei = U einR, Ueo = U eoutR, UP = U P, Ur = U rest):
  --   σ-in  = (id{UP} ⊗ to(uf++ einR rest)) ∘ α⇒ ∘ (σ{Uei}{UP} ⊗ id{Ur})
  --             ∘ α⇐ ∘ (id{Uei} ⊗ from(uf++ P rest)) ∘ from(uf++ einR (P++rest))
  --   σ-out = to(uf++ eoutR (P++rest)) ∘ (id{Ueo} ⊗ to(uf++ P rest)) ∘ α⇒
  --             ∘ (σ{UP}{Ueo} ⊗ id{Ur}) ∘ α⇐ ∘ (id{UP} ⊗ from(uf++ eoutR rest)).
  --
  -- The move is the PROVEN one-box symmetry-naturality `σ∘[f⊗g]≈[g⊗f]∘σ`
  -- (the single generator `G = Agen g` slid past the identity block `id{UP}`)
  -- plus `σ∘σ≈id` and the α-coherence (`α-comm`, `α⇒∘α⇐≈id`, `α⇐∘α⇒≈id`)
  -- framing.  It is the `N`+`M` content, NOT the two-box `nf-bracket` kernel.
  box-braid
    : ∀ (P einR eoutR rest : List X) (g : FlatGen einR eoutR)
    → box-of einR eoutR (P ++ rest) g
      ≈Term
        ( _≅_.to (unflatten-++-≅ eoutR (P ++ rest))
          ∘ (id {unflatten eoutR} ⊗₁ _≅_.to (unflatten-++-≅ P rest))
          ∘ α⇒ {unflatten eoutR} {unflatten P} {unflatten rest}
          ∘ (σ {unflatten P} {unflatten eoutR} ⊗₁ id {unflatten rest})
          ∘ α⇐ {unflatten P} {unflatten eoutR} {unflatten rest}
          ∘ (id {unflatten P} ⊗₁ _≅_.from (unflatten-++-≅ eoutR rest)) )
      ∘ (id {unflatten P} ⊗₁ box-of einR eoutR rest g)
      ∘ ( (id {unflatten P} ⊗₁ _≅_.to (unflatten-++-≅ einR rest))
          ∘ α⇒ {unflatten P} {unflatten einR} {unflatten rest}
          ∘ (σ {unflatten einR} {unflatten P} ⊗₁ id {unflatten rest})
          ∘ α⇐ {unflatten einR} {unflatten P} {unflatten rest}
          ∘ (id {unflatten einR} ⊗₁ _≅_.from (unflatten-++-≅ P rest))
          ∘ _≅_.from (unflatten-++-≅ einR (P ++ rest)) )
  box-braid P einR eoutR rest g = ≈-Term-sym rhs-chase
    where
      G   = Agen-edge-aux g
      UP  = unflatten P
      Uei = unflatten einR
      Ueo = unflatten eoutR
      Ur  = unflatten rest
      UPr = unflatten (P ++ rest)

      -- the framing isos.
      to-eo-Prest   = _≅_.to   (unflatten-++-≅ eoutR (P ++ rest))
      from-ei-Prest = _≅_.from (unflatten-++-≅ einR  (P ++ rest))
      to-P-rest     = _≅_.to   (unflatten-++-≅ P rest)
      from-P-rest   = _≅_.from (unflatten-++-≅ P rest)
      to-ei-rest    = _≅_.to   (unflatten-++-≅ einR  rest)
      from-ei-rest  = _≅_.from (unflatten-++-≅ einR  rest)
      to-eo-rest    = _≅_.to   (unflatten-++-≅ eoutR rest)
      from-eo-rest  = _≅_.from (unflatten-++-≅ eoutR rest)

      box  = to-eo-rest ∘ (G ⊗₁ id {Ur}) ∘ from-ei-rest
      boxR = to-eo-Prest ∘ (G ⊗₁ id {UPr}) ∘ from-ei-Prest   -- = box-of … (P++rest)

      σ-in =
            (id {UP} ⊗₁ to-ei-rest)
          ∘ α⇒ {UP} {Uei} {Ur}
          ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest

      σ-out =
            to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
          ∘ α⇐ {UP} {Ueo} {Ur}
          ∘ (id {UP} ⊗₁ from-eo-rest)

      -- (1) FRONT collapse: the eo-/ei-rest framing inside `id{UP} ⊗ box`
      --     cancels the `id{UP} ⊗ from-eo-rest` / `id{UP} ⊗ to-ei-rest`
      --     factors, leaving `id{UP} ⊗ (G ⊗ id{Ur})`.
      front-collapse
        : (id {UP} ⊗₁ from-eo-rest)
          ∘ (id {UP} ⊗₁ box)
          ∘ (id {UP} ⊗₁ to-ei-rest)
          ≈Term id {UP} ⊗₁ (G ⊗₁ id {Ur})
      front-collapse = begin
        (id {UP} ⊗₁ from-eo-rest)
          ∘ (id {UP} ⊗₁ box)
          ∘ (id {UP} ⊗₁ to-ei-rest)
          ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (id {UP} ⊗₁ from-eo-rest)
          ∘ ((id ∘ id) ⊗₁ (box ∘ to-ei-rest))
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
        (id {UP} ⊗₁ from-eo-rest)
          ∘ (id ⊗₁ (box ∘ to-ei-rest))
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (id ∘ id) ⊗₁ (from-eo-rest ∘ box ∘ to-ei-rest)
          ≈⟨ ⊗-resp-≈ idˡ inner ⟩
        id {UP} ⊗₁ (G ⊗₁ id {Ur}) ∎
        where
          inner : from-eo-rest ∘ box ∘ to-ei-rest ≈Term G ⊗₁ id {Ur}
          inner = begin
            from-eo-rest ∘ (to-eo-rest ∘ (G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            from-eo-rest ∘ to-eo-rest ∘ ((G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ FM.sym-assoc ⟩
            (from-eo-rest ∘ to-eo-rest) ∘ ((G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ _≅_.isoʳ (unflatten-++-≅ eoutR rest) ⟩∘⟨refl ⟩
            id ∘ ((G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ idˡ ⟩
            ((G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ FM.assoc ⟩
            (G ⊗₁ id {Ur}) ∘ (from-ei-rest ∘ to-ei-rest)
              ≈⟨ refl⟩∘⟨ _≅_.isoʳ (unflatten-++-≅ einR rest) ⟩
            (G ⊗₁ id {Ur}) ∘ id
              ≈⟨ idʳ ⟩
            G ⊗₁ id {Ur} ∎

      -- (2) CENTRAL collapse: `α⇐{UP}{Ueo}{Ur} ∘ (id{UP}⊗(G⊗id{Ur})) ∘ α⇒{UP}{Uei}{Ur}`
      --     collapses via α-comm + α⇐∘α⇒≈id to `(id{UP}⊗G) ⊗ id{Ur}`.
      central-collapse
        : α⇐ {UP} {Ueo} {Ur}
          ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
          ∘ α⇒ {UP} {Uei} {Ur}
          ≈Term (id {UP} ⊗₁ G) ⊗₁ id {Ur}
      central-collapse = begin
        α⇐ {UP} {Ueo} {Ur}
          ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
          ∘ α⇒ {UP} {Uei} {Ur}
          ≈⟨ refl⟩∘⟨ ≈-Term-sym α-comm ⟩
        α⇐ {UP} {Ueo} {Ur}
          ∘ α⇒ {UP} {Ueo} {Ur}
          ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
          ≈⟨ FM.sym-assoc ⟩
        (α⇐ {UP} {Ueo} {Ur} ∘ α⇒ {UP} {Ueo} {Ur})
          ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
          ≈⟨ α⇐∘α⇒≈id ⟩∘⟨refl ⟩
        id ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
          ≈⟨ idˡ ⟩
        (id {UP} ⊗₁ G) ⊗₁ id {Ur} ∎

      -- (3) σ-SLIDE: the ONE-BOX symmetry-naturality move.  The generator
      --     `G` slides through the two braids `σ{UP}{Ueo}` / `σ{Uei}{UP}`,
      --     which then cancel via `σ∘σ≈id`, leaving `G ⊗ id{UP}`.
      sigma-slide
        : σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G) ∘ σ {Uei} {UP}
          ≈Term G ⊗₁ id {UP}
      sigma-slide = begin
        σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G) ∘ σ {Uei} {UP}
          ≈⟨ FM.sym-assoc ⟩
        (σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G)) ∘ σ {Uei} {UP}
          ≈⟨ σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl ⟩
        ((G ⊗₁ id {UP}) ∘ σ {UP} {Uei}) ∘ σ {Uei} {UP}
          ≈⟨ FM.assoc ⟩
        (G ⊗₁ id {UP}) ∘ (σ {UP} {Uei} ∘ σ {Uei} {UP})
          ≈⟨ refl⟩∘⟨ σ∘σ≈id ⟩
        (G ⊗₁ id {UP}) ∘ id
          ≈⟨ idʳ ⟩
        G ⊗₁ id {UP} ∎

      -- (4) TAIL collapse: the eo-side framing (`α⇒{Ueo}{UP}{Ur}` past the
      --     output `G⊗id{UP}`, then the `id{Ueo}⊗to-P-rest` / `id{Uei}⊗from-P-rest`
      --     framings) collapses `(G⊗id{UP}) ⊗ id{Ur}` into `G ⊗ id{UPr}`,
      --     framed by `to-P-rest`/`from-P-rest`.
      tail-collapse
        : (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈Term G ⊗₁ id {UPr}
      tail-collapse = begin
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          -- slide `α⇒ ∘ ((G⊗id{UP})⊗id{Ur})` to `(G⊗(id{UP}⊗id{Ur})) ∘ α⇒`.
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ (α⇒ {Ueo} {UP} {Ur} ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur}))
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ ((G ⊗₁ (id {UP} ⊗₁ id {Ur})) ∘ α⇒ {Uei} {UP} {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ ((G ⊗₁ id {UP ⊗₀ Ur}) ∘ α⇒ {Uei} {UP} {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          -- cancel `α⇒ ∘ α⇐ = id`.
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ (G ⊗₁ id {UP ⊗₀ Ur})
          ∘ α⇒ {Uei} {UP} {Ur}
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ (G ⊗₁ id {UP ⊗₀ Ur})
          ∘ (α⇒ {Uei} {UP} {Ur} ∘ α⇐ {Uei} {UP} {Ur})
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ (G ⊗₁ id {UP ⊗₀ Ur})
          ∘ id
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        (id {Ueo} ⊗₁ to-P-rest)
          ∘ (G ⊗₁ id {UP ⊗₀ Ur})
          ∘ (id {Uei} ⊗₁ from-P-rest)
          -- collapse the two ⊗-framings around the generator.
          ≈⟨ FM.sym-assoc ⟩
        ((id {Ueo} ⊗₁ to-P-rest) ∘ (G ⊗₁ id {UP ⊗₀ Ur}))
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
        ((id {Ueo} ∘ G) ⊗₁ (to-P-rest ∘ id {UP ⊗₀ Ur}))
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ ⊗-resp-≈ idˡ idʳ ⟩∘⟨refl ⟩
        (G ⊗₁ to-P-rest) ∘ (id {Uei} ⊗₁ from-P-rest)
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (G ∘ id {Uei}) ⊗₁ (to-P-rest ∘ from-P-rest)
          ≈⟨ ⊗-resp-≈ idʳ (_≅_.isoˡ (unflatten-++-≅ P rest)) ⟩
        G ⊗₁ id {UPr} ∎

      -- the master chain: σ-out ∘ (id{UP} ⊗ box) ∘ σ-in ≈ boxR.
      rhs-chase
        : σ-out ∘ (id {UP} ⊗₁ box) ∘ σ-in ≈Term boxR
      rhs-chase = begin
        σ-out ∘ (id {UP} ⊗₁ box) ∘ σ-in
          -- Step A: regroup so the `(id{UP}⊗from-eo-rest)/(id{UP}⊗box)/
          --   (id{UP}⊗to-ei-rest)` front-triple is adjacent, then collapse it.
          ≈⟨ regroup-front ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
          ∘ α⇐ {UP} {Ueo} {Ur}
          ∘ ((id {UP} ⊗₁ from-eo-rest)
             ∘ (id {UP} ⊗₁ box)
             ∘ (id {UP} ⊗₁ to-ei-rest))
          ∘ α⇒ {UP} {Uei} {Ur}
          ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ front-collapse ⟩∘⟨refl ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
          ∘ α⇐ {UP} {Ueo} {Ur}
          ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
          ∘ α⇒ {UP} {Uei} {Ur}
          ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          -- Step B: regroup the central `α⇐{UP}{Ueo}{Ur} ∘ (id{UP}⊗(G⊗id{Ur}))
          --   ∘ α⇒{UP}{Uei}{Ur}` triple adjacent, then collapse it.
          ≈⟨ regroup-central ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
          ∘ (α⇐ {UP} {Ueo} {Ur}
             ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
             ∘ α⇒ {UP} {Uei} {Ur})
          ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ central-collapse ⟩∘⟨refl ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
          ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
          ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          -- Step C: fuse the three `_ ⊗ id{Ur}` factors, run the σ-slide.
          ≈⟨ regroup-sigma ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ ((σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G) ∘ σ {Uei} {UP}) ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ sigma-slide ≈-Term-refl ⟩∘⟨refl ⟩
        to-eo-Prest
          ∘ (id {Ueo} ⊗₁ to-P-rest)
          ∘ α⇒ {Ueo} {UP} {Ur}
          ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
          ∘ α⇐ {Uei} {UP} {Ur}
          ∘ (id {Uei} ⊗₁ from-P-rest)
          ∘ from-ei-Prest
          -- Step D: regroup the tail-collapse quintuple adjacent, collapse it.
          ≈⟨ regroup-tail ⟩
        to-eo-Prest
          ∘ ((id {Ueo} ⊗₁ to-P-rest)
             ∘ α⇒ {Ueo} {UP} {Ur}
             ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
             ∘ α⇐ {Uei} {UP} {Ur}
             ∘ (id {Uei} ⊗₁ from-P-rest))
          ∘ from-ei-Prest
          ≈⟨ refl⟩∘⟨ tail-collapse ⟩∘⟨refl ⟩
        to-eo-Prest ∘ (G ⊗₁ id {UPr}) ∘ from-ei-Prest ∎
        where
          -- pure-associativity reshuffles (the `≈⟨ ⟩` glue between collapses).
          regroup-front
            : σ-out ∘ (id {UP} ⊗₁ box) ∘ σ-in
            ≈Term
              to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                ∘ α⇐ {UP} {Ueo} {Ur}
                ∘ ((id {UP} ⊗₁ from-eo-rest)
                   ∘ (id {UP} ⊗₁ box)
                   ∘ (id {UP} ⊗₁ to-ei-rest))
                ∘ α⇒ {UP} {Uei} {Ur}
                ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
          regroup-front = begin
            σ-out ∘ (id {UP} ⊗₁ box) ∘ σ-in
              -- flatten σ-out's leading factor off (assoc cascade).
              ≈⟨ FM.assoc ⟩
            to-eo-Prest
              ∘ ((id {Ueo} ⊗₁ to-P-rest)
                 ∘ α⇒ {Ueo} {UP} {Ur}
                 ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                 ∘ α⇐ {UP} {Ueo} {Ur}
                 ∘ (id {UP} ⊗₁ from-eo-rest))
              ∘ (id {UP} ⊗₁ box) ∘ σ-in
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            to-eo-Prest
              ∘ (id {Ueo} ⊗₁ to-P-rest)
              ∘ (α⇒ {Ueo} {UP} {Ur}
                 ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                 ∘ α⇐ {UP} {Ueo} {Ur}
                 ∘ (id {UP} ⊗₁ from-eo-rest))
              ∘ (id {UP} ⊗₁ box) ∘ σ-in
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            to-eo-Prest
              ∘ (id {Ueo} ⊗₁ to-P-rest)
              ∘ α⇒ {Ueo} {UP} {Ur}
              ∘ ((σ {UP} {Ueo} ⊗₁ id {Ur})
                 ∘ α⇐ {UP} {Ueo} {Ur}
                 ∘ (id {UP} ⊗₁ from-eo-rest))
              ∘ (id {UP} ⊗₁ box) ∘ σ-in
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            to-eo-Prest
              ∘ (id {Ueo} ⊗₁ to-P-rest)
              ∘ α⇒ {Ueo} {UP} {Ur}
              ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
              ∘ (α⇐ {UP} {Ueo} {Ur}
                 ∘ (id {UP} ⊗₁ from-eo-rest))
              ∘ (id {UP} ⊗₁ box) ∘ σ-in
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            to-eo-Prest
              ∘ (id {Ueo} ⊗₁ to-P-rest)
              ∘ α⇒ {Ueo} {UP} {Ur}
              ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
              ∘ α⇐ {UP} {Ueo} {Ur}
              ∘ (id {UP} ⊗₁ from-eo-rest)
              ∘ (id {UP} ⊗₁ box) ∘ σ-in
              -- now expose & group the front-triple via `middle`.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ middle ⟩
            to-eo-Prest
              ∘ (id {Ueo} ⊗₁ to-P-rest)
              ∘ α⇒ {Ueo} {UP} {Ur}
              ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
              ∘ α⇐ {UP} {Ueo} {Ur}
              ∘ ((id {UP} ⊗₁ from-eo-rest)
                 ∘ (id {UP} ⊗₁ box)
                 ∘ (id {UP} ⊗₁ to-ei-rest))
              ∘ α⇒ {UP} {Uei} {Ur}
              ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
              ∘ α⇐ {Uei} {UP} {Ur}
              ∘ (id {Uei} ⊗₁ from-P-rest)
              ∘ from-ei-Prest ∎
            where
              -- the only non-trivial part: re-associate
              --   (id{UP}⊗from-eo-rest) ∘ [ (id{UP}⊗box) ∘ σ-in-tail ]
              -- so the front-triple is parenthesised.  Everything else is the
              -- definitional unfolding of σ-out / σ-in (already aligned).
              middle
                : (id {UP} ⊗₁ from-eo-rest)
                  ∘ (id {UP} ⊗₁ box)
                  ∘ ((id {UP} ⊗₁ to-ei-rest)
                     ∘ α⇒ {UP} {Uei} {Ur}
                     ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                     ∘ α⇐ {Uei} {UP} {Ur}
                     ∘ (id {Uei} ⊗₁ from-P-rest)
                     ∘ from-ei-Prest)
                ≈Term
                  ((id {UP} ⊗₁ from-eo-rest)
                   ∘ (id {UP} ⊗₁ box)
                   ∘ (id {UP} ⊗₁ to-ei-rest))
                  ∘ α⇒ {UP} {Uei} {Ur}
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
              middle = begin
                (id {UP} ⊗₁ from-eo-rest)
                  ∘ (id {UP} ⊗₁ box)
                  ∘ ((id {UP} ⊗₁ to-ei-rest) ∘ tail)
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                (id {UP} ⊗₁ from-eo-rest)
                  ∘ ((id {UP} ⊗₁ box) ∘ (id {UP} ⊗₁ to-ei-rest))
                  ∘ tail
                  ≈⟨ FM.sym-assoc ⟩
                ((id {UP} ⊗₁ from-eo-rest)
                  ∘ ((id {UP} ⊗₁ box) ∘ (id {UP} ⊗₁ to-ei-rest)))
                  ∘ tail
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                (((id {UP} ⊗₁ from-eo-rest) ∘ (id {UP} ⊗₁ box))
                  ∘ (id {UP} ⊗₁ to-ei-rest))
                  ∘ tail
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                ((id {UP} ⊗₁ from-eo-rest)
                  ∘ (id {UP} ⊗₁ box)
                  ∘ (id {UP} ⊗₁ to-ei-rest))
                  ∘ α⇒ {UP} {Uei} {Ur}
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest ∎
                where
                  tail =
                      α⇒ {UP} {Uei} {Ur}
                    ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                    ∘ α⇐ {Uei} {UP} {Ur}
                    ∘ (id {Uei} ⊗₁ from-P-rest)
                    ∘ from-ei-Prest

          regroup-central
            : to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                ∘ α⇐ {UP} {Ueo} {Ur}
                ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
                ∘ α⇒ {UP} {Uei} {Ur}
                ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
            ≈Term
              to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                ∘ (α⇐ {UP} {Ueo} {Ur}
                   ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
                   ∘ α⇒ {UP} {Uei} {Ur})
                ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
          regroup-central =
            refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
              (begin
                α⇐ {UP} {Ueo} {Ur}
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
                  ∘ α⇒ {UP} {Uei} {Ur}
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                α⇐ {UP} {Ueo} {Ur}
                  ∘ ((id {UP} ⊗₁ (G ⊗₁ id {Ur})) ∘ α⇒ {UP} {Uei} {Ur})
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
                  ≈⟨ FM.sym-assoc ⟩
                (α⇐ {UP} {Ueo} {Ur}
                  ∘ ((id {UP} ⊗₁ (G ⊗₁ id {Ur})) ∘ α⇒ {UP} {Uei} {Ur}))
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                ((α⇐ {UP} {Ueo} {Ur} ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur})))
                  ∘ α⇒ {UP} {Uei} {Ur})
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                (α⇐ {UP} {Ueo} {Ur}
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Ur}))
                  ∘ α⇒ {UP} {Uei} {Ur})
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest ∎)

          regroup-sigma
            : to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ (σ {UP} {Ueo} ⊗₁ id {Ur})
                ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
                ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
            ≈Term
              to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ ((σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G) ∘ σ {Uei} {UP}) ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
          regroup-sigma =
            refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
              (begin
                (σ {UP} {Ueo} ⊗₁ id {Ur})
                  ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Ur})
                  ∘ (σ {Uei} {UP} ⊗₁ id {Ur})
                  ∘ rest-tail
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                (σ {UP} {Ueo} ⊗₁ id {Ur})
                  ∘ (((id {UP} ⊗₁ G) ⊗₁ id {Ur}) ∘ (σ {Uei} {UP} ⊗₁ id {Ur}))
                  ∘ rest-tail
                  ≈⟨ FM.sym-assoc ⟩
                ((σ {UP} {Ueo} ⊗₁ id {Ur})
                  ∘ (((id {UP} ⊗₁ G) ⊗₁ id {Ur}) ∘ (σ {Uei} {UP} ⊗₁ id {Ur})))
                  ∘ rest-tail
                  ≈⟨ (refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist) ⟩∘⟨refl ⟩
                ((σ {UP} {Ueo} ⊗₁ id {Ur})
                  ∘ (((id {UP} ⊗₁ G) ∘ σ {Uei} {UP}) ⊗₁ (id {Ur} ∘ id {Ur})))
                  ∘ rest-tail
                  ≈⟨ (refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ) ⟩∘⟨refl ⟩
                ((σ {UP} {Ueo} ⊗₁ id {Ur})
                  ∘ (((id {UP} ⊗₁ G) ∘ σ {Uei} {UP}) ⊗₁ id {Ur}))
                  ∘ rest-tail
                  ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
                ((σ {UP} {Ueo} ∘ ((id {UP} ⊗₁ G) ∘ σ {Uei} {UP}))
                  ⊗₁ (id {Ur} ∘ id {Ur}))
                  ∘ rest-tail
                  ≈⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩∘⟨refl ⟩
                ((σ {UP} {Ueo} ∘ (id {UP} ⊗₁ G) ∘ σ {Uei} {UP}) ⊗₁ id {Ur})
                  ∘ rest-tail ∎)
            where
              rest-tail =
                  α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest

          regroup-tail
            : to-eo-Prest
                ∘ (id {Ueo} ⊗₁ to-P-rest)
                ∘ α⇒ {Ueo} {UP} {Ur}
                ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
                ∘ α⇐ {Uei} {UP} {Ur}
                ∘ (id {Uei} ⊗₁ from-P-rest)
                ∘ from-ei-Prest
            ≈Term
              to-eo-Prest
                ∘ ((id {Ueo} ⊗₁ to-P-rest)
                   ∘ α⇒ {Ueo} {UP} {Ur}
                   ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
                   ∘ α⇐ {Uei} {UP} {Ur}
                   ∘ (id {Uei} ⊗₁ from-P-rest))
                ∘ from-ei-Prest
          regroup-tail =
            refl⟩∘⟨
              (begin
                (id {Ueo} ⊗₁ to-P-rest)
                  ∘ α⇒ {Ueo} {UP} {Ur}
                  ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest)
                  ∘ from-ei-Prest
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                (id {Ueo} ⊗₁ to-P-rest)
                  ∘ α⇒ {Ueo} {UP} {Ur}
                  ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
                  ∘ (α⇐ {Uei} {UP} {Ur} ∘ (id {Uei} ⊗₁ from-P-rest))
                  ∘ from-ei-Prest
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                (id {Ueo} ⊗₁ to-P-rest)
                  ∘ α⇒ {Ueo} {UP} {Ur}
                  ∘ (((G ⊗₁ id {UP}) ⊗₁ id {Ur}) ∘ (α⇐ {Uei} {UP} {Ur} ∘ (id {Uei} ⊗₁ from-P-rest)))
                  ∘ from-ei-Prest
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                (id {Ueo} ⊗₁ to-P-rest)
                  ∘ (α⇒ {Ueo} {UP} {Ur} ∘ (((G ⊗₁ id {UP}) ⊗₁ id {Ur}) ∘ (α⇐ {Uei} {UP} {Ur} ∘ (id {Uei} ⊗₁ from-P-rest))))
                  ∘ from-ei-Prest
                  ≈⟨ FM.sym-assoc ⟩
                ((id {Ueo} ⊗₁ to-P-rest)
                  ∘ (α⇒ {Ueo} {UP} {Ur} ∘ (((G ⊗₁ id {UP}) ⊗₁ id {Ur}) ∘ (α⇐ {Uei} {UP} {Ur} ∘ (id {Uei} ⊗₁ from-P-rest)))))
                  ∘ from-ei-Prest
                  ≈⟨ ≈-Term-refl ⟩∘⟨refl ⟩
                ((id {Ueo} ⊗₁ to-P-rest)
                  ∘ α⇒ {Ueo} {UP} {Ur}
                  ∘ ((G ⊗₁ id {UP}) ⊗₁ id {Ur})
                  ∘ α⇐ {Uei} {UP} {Ur}
                  ∘ (id {Uei} ⊗₁ from-P-rest))
                  ∘ from-ei-Prest ∎)

--------------------------------------------------------------------------------
-- ## The GENERIC `vlab`-framed box-suffix reframe.
--
-- `BoxAssoc.box-suffix` reframed into the `BlockTensor vlab` `uf++`
-- convention, GENERIC in the residual suffix block `Rblk : List (Fin n)`.
-- This is the shared kernel of `BlockFactor.box-suffix-BTC` (with `vlab =
-- C.vlab`, `Rblk = map injR ys`) and `BlockNFNf2.box-suffix-BNf` (with `vlab
-- = H.vlab`, `Rblk = R`): both are `map vlab Rblk` suffixes over a single
-- block-tensor framing, and so are this one lemma at two instantiations.
--
-- Postulate-free, hole-free: pure `++-assoc` / `map-++` framing bookkeeping
-- bridging `box-of` on the SPLIT residual `map vlab rgBlk ++ map vlab Rblk`
-- to the `BT.uf++`-framed `(box-of on map vlab rgBlk) ⊗₁ id` on the WHOLE
-- block lists `eoBlk++rgBlk` / `eiBlk++rgBlk`.

module BlockBoxSuffix
  {n : ℕ} (vlab : Fin n → X)
  where
  open FM.HomReasoning
  private
    module BT = BlockTensor vlab

    -- to/from of `BT.uf++ As Bs` in terms of the raw `unflatten-++-≅`.
    to-BTC : ∀ (As Bs : List (Fin n))
           → _≅_.to (BT.uf++ As Bs)
             ≡ subst₂ HomTerm refl (cong unflatten (sym (map-++ vlab As Bs)))
                 (_≅_.to (unflatten-++-≅ (map vlab As) (map vlab Bs)))
    to-BTC As Bs = BNB.to-subst₂-≅ (cong unflatten (sym (map-++ vlab As Bs)))
                     (unflatten-++-≅ (map vlab As) (map vlab Bs))

    from-BTC : ∀ (As Bs : List (Fin n))
             → _≅_.from (BT.uf++ As Bs)
               ≡ subst₂ HomTerm (cong unflatten (sym (map-++ vlab As Bs))) refl
                   (_≅_.from (unflatten-++-≅ (map vlab As) (map vlab Bs)))
    from-BTC As Bs = BNB.from-subst₂-≅ (cong unflatten (sym (map-++ vlab As Bs)))
                       (unflatten-++-≅ (map vlab As) (map vlab Bs))

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
    -- `map-++ vlab` layers, one per box endpoint block.
    whole-eq : ∀ (lBlk rgBlk Rblk : List (Fin n))
             → map vlab lBlk ++ (map vlab rgBlk ++ map vlab Rblk)
               ≡ map vlab ((lBlk ++ rgBlk) ++ Rblk)
    whole-eq lBlk rgBlk Rblk =
      trans (sym (++-assoc (map vlab lBlk) (map vlab rgBlk) (map vlab Rblk)))
      (trans (cong (_++ map vlab Rblk) (sym (map-++ vlab lBlk rgBlk)))
             (sym (map-++ vlab (lBlk ++ rgBlk) Rblk)))

  -- `box-suffix` reframed into `BT.uf++`, generic in the suffix block `Rblk`.
  box-suffix-framed
    : ∀ (eiBlk eoBlk rgBlk Rblk : List (Fin n))
        (g : FlatGen (map vlab eiBlk) (map vlab eoBlk))
    → subst₂ HomTerm
        (cong unflatten (whole-eq eiBlk rgBlk Rblk))
        (cong unflatten (whole-eq eoBlk rgBlk Rblk))
        (box-of (map vlab eiBlk) (map vlab eoBlk)
                (map vlab rgBlk ++ map vlab Rblk) g)
      ≈Term _≅_.to (BT.uf++ (eoBlk ++ rgBlk) Rblk)
            ∘ (subst₂ HomTerm
                 (cong unflatten (sym (map-++ vlab eiBlk rgBlk)))
                 (cong unflatten (sym (map-++ vlab eoBlk rgBlk)))
                 (box-of (map vlab eiBlk) (map vlab eoBlk) (map vlab rgBlk) g)
                 ⊗₁ id {BT.R-obj Rblk})
            ∘ _≅_.from (BT.uf++ (eiBlk ++ rgBlk) Rblk)
  box-suffix-framed eiBlk eoBlk rgBlk Rblk g =
    ≈-Term-trans (≡⇒≈Term decomp)
      (≈-Term-trans (subst₂-resp-≈Term (cong unflatten Cei) (cong unflatten Ceo)
                       (subst₂-resp-≈Term (cong unflatten Bei) (cong unflatten Beo)
                          (BoxAssoc.box-suffix
                             (map vlab eiBlk) (map vlab eoBlk)
                             (map vlab rgBlk) (map vlab Rblk) g)))
                    reframe)
    where
      eiL = map vlab eiBlk
      eoL = map vlab eoBlk
      rgL = map vlab rgBlk
      RL  = map vlab Rblk

      Aei = sym (++-assoc eiL rgL RL)
      Aeo = sym (++-assoc eoL rgL RL)
      Bei = cong (_++ RL) (sym (map-++ vlab eiBlk rgBlk))
      Beo = cong (_++ RL) (sym (map-++ vlab eoBlk rgBlk))
      Cei = sym (map-++ vlab (eiBlk ++ rgBlk) Rblk)
      Ceo = sym (map-++ vlab (eoBlk ++ rgBlk) Rblk)

      decomp :
        subst₂ HomTerm
          (cong unflatten (whole-eq eiBlk rgBlk Rblk))
          (cong unflatten (whole-eq eoBlk rgBlk Rblk))
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
          cong-whole : ∀ (lBlk : List (Fin n))
                     → cong unflatten (whole-eq lBlk rgBlk Rblk)
                       ≡ trans (cong unflatten (sym (++-assoc (map vlab lBlk) rgL RL)))
                           (trans (cong unflatten (cong (_++ RL) (sym (map-++ vlab lBlk rgBlk))))
                                  (cong unflatten (sym (map-++ vlab (lBlk ++ rgBlk) Rblk))))
          cong-whole lBlk =
            trans (sym (trans-cong {f = unflatten}
                          (sym (++-assoc (map vlab lBlk) rgL RL))))
                  (cong (trans (cong unflatten (sym (++-assoc (map vlab lBlk) rgL RL))))
                        (sym (trans-cong {f = unflatten}
                                (cong (_++ RL) (sym (map-++ vlab lBlk rgBlk))))))

      reframe :
        subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
          (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
             (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL)
               ∘ (box-of eiL eoL rgL g ⊗₁ id {unflatten RL})
               ∘ _≅_.from (unflatten-++-≅ (eiL ++ rgL) RL)))
        ≈Term _≅_.to (BT.uf++ (eoBlk ++ rgBlk) Rblk)
              ∘ (subst₂ HomTerm
                   (cong unflatten (sym (map-++ vlab eiBlk rgBlk)))
                   (cong unflatten (sym (map-++ vlab eoBlk rgBlk)))
                   (box-of eiL eoL rgL g)
                   ⊗₁ id {BT.R-obj Rblk})
              ∘ _≅_.from (BT.uf++ (eiBlk ++ rgBlk) Rblk)
      reframe = ≈-Term-sym (≡⇒≈Term rhs-≡)
        where
          eirg = eiBlk ++ rgBlk
          eorg = eoBlk ++ rgBlk
          UR   = unflatten RL

          boxRg = box-of eiL eoL rgL g

          mpei = sym (map-++ vlab eiBlk rgBlk)
          mpeo = sym (map-++ vlab eoBlk rgBlk)

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
            _≅_.to (BT.uf++ eorg Rblk)
            ≡ subst₂ HomTerm
                (trans (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl)
                (trans (cong (λ z → unflatten (z ++ RL)) mpeo) (cong unflatten Ceo))
                (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL))
          to-eo-≡ =
            trans (to-BTC eorg Rblk)
            (trans (cong (subst₂ HomTerm refl (cong unflatten Ceo))
                         (trans (sym (to-blk1 RL (eoL ++ rgL) (map vlab eorg) mpeo))
                                (subst-2 (λ z → unflatten z ⊗₀ UR) (λ z → unflatten (z ++ RL))
                                   mpeo
                                   (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL)))))
                   (subst₂-HomTerm-∘
                      (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl
                      (cong (λ z → unflatten (z ++ RL)) mpeo) (cong unflatten Ceo)
                      (_≅_.to (unflatten-++-≅ (eoL ++ rgL) RL))))

          from-ei-≡ :
            _≅_.from (BT.uf++ eirg Rblk)
            ≡ subst₂ HomTerm
                (trans (cong (λ z → unflatten (z ++ RL)) mpei) (cong unflatten Cei))
                (trans (cong (λ z → unflatten z ⊗₀ UR) mpei) refl)
                (_≅_.from (unflatten-++-≅ (eiL ++ rgL) RL))
          from-ei-≡ =
            trans (from-BTC eirg Rblk)
            (trans (cong (subst₂ HomTerm (cong unflatten Cei) refl)
                         (trans (sym (from-blk1 RL (eiL ++ rgL) (map vlab eirg) mpei))
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
                    ⊗₁ id {BT.R-obj Rblk}
                  ≡ subst₂ HomTerm Qfr Qto M
          mid-≡ =
            trans (⊗-push mpei mpeo boxRg)
                  (cong₂ (λ p q → subst₂ HomTerm p q M)
                         (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpei)))
                         (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpeo))))

          rhs-≡ :
            _≅_.to (BT.uf++ eorg Rblk)
              ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                   ⊗₁ id {BT.R-obj Rblk})
              ∘ _≅_.from (BT.uf++ eirg Rblk)
            ≡ subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                   (to-raw ∘ M ∘ fr-raw))
          rhs-≡ = ≡R.begin
              _≅_.to (BT.uf++ eorg Rblk)
                ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                     ⊗₁ id {BT.R-obj Rblk})
                ∘ _≅_.from (BT.uf++ eirg Rblk)
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
              subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                   (to-raw ∘ M ∘ fr-raw)) ≡R.∎
            where
              module ≡R = ≡-Reasoning
              cong₃ : ∀ {a} {A B C D : Set a} (f : A → B → C → D)
                        {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z'
                      → f x y z ≡ f x' y' z'
              cong₃ f refl refl refl = refl

--------------------------------------------------------------------------------
-- ## The G-side / K-side block factorizations — SHARED SCAFFOLDING.
--
-- Postulate-free, hole-free.  The G-side TERM companion of the
-- STACK-only `process-edges-↑ˡ-on-mixed` — `gblock-factor` (Milestone 2a) —
-- is assembled below, along with the σ-mirror per-FIRE-edge tool
-- `box-braid-pvl` (Milestone 1, front→prefix in `pvlC` form).  The K-side
-- companion of `process-edges-↑ʳ-on-perm` — `kblock-factor` (Milestone 2b) —
-- is assembled from its base-case scaffolding `KClean-nil`/`pvlC-cancel`.
-- This module fixes the framing convention (`BTC.uf++`, matching
-- `pvv-block-tensor`) and the
-- factored-form shapes (`GFactored`, `Lterm`, `KFactored`, `KClean`, `Kterm`)
-- those inductions land on, plus the stack agreements (`mixed-stack-G`,
-- `proc-stack-emb-L`/`-R`) and the per-edge `box-of` residual-rewrite
-- (`box-rest-rewrite`) they consume.

module BlockFactor
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  (G K : Hypergraph FlatGen)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open FA.hTensor-impl G K
  open FM.HomReasoning
  open EmbedData objUIP Kf G K using (module TG; module TK)

  C-hg : Hypergraph FlatGen
  C-hg = hTensor G K

  -- Abbreviations for the C-level run.
  pe-stackC : List (Fin C.nE) → List (Fin C.nV) → List (Fin C.nV)
  pe-stackC o s = proj₁ (process-edges C-hg o s)

  pe-termC : (o : List (Fin C.nE)) (s : List (Fin C.nV))
           → HomTerm (unflatten (map C.vlab s))
                     (unflatten (map C.vlab (pe-stackC o s)))
  pe-termC o s = proj₂ (process-edges C-hg o s)


  ------------------------------------------------------------------------
  -- ### Milestone 2a — the G-side SUFFIX-CARRY factorization.
  --
  -- The whole factorization is at the C level (no G/K relabel — that is the
  -- gate's job later).  We relate the mixed-stack C-run of the G-edge block
  -- to the pure-L C-run tensored with `id` on the (constant) `map injR ys`
  -- suffix, framed by the raw `unflatten-++-≅` on the `vlab-c`-images.
  --
  -- Per FIRE edge the box-of on residual `map vlab-c (map injL restG) ++
  -- map vlab-c (map injR ys)` factors as `(box-of on map vlab-c (map injL
  -- restG)) ⊗₁ id` via `BoxAssoc.box-suffix`; per SKIP edge the `id` factors
  -- as `id ⊗₁ id`.  The `permute` of each FIRE step (the `pvl perm`) carries
  -- along.  This is the term companion of `process-edges-↑ˡ-on-mixed`.

  -- The `BlockTensor C.vlab` framing (matches `pvv-block-tensor`'s `uf++`).
  module BTC = BlockTensor C.vlab

  -- The generic `vlab`-framed box-suffix reframe, instantiated at `C.vlab`;
  -- `box-suffix-BTC` is its `Rblk = map injR ys` instance.
  module BBSC = BlockBoxSuffix C.vlab

  -- Codomain transport along a C-stack equality.
  coeC : ∀ {d : List (Fin C.nV)} {s s' : List (Fin C.nV)} → s ≡ s'
       → HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s))
       → HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s'))
  coeC {d} eq = subst (λ z → HomTerm (unflatten (map C.vlab d))
                                      (unflatten (map C.vlab z))) eq

  ------------------------------------------------------------------------
  -- `box-of` residual-list rewrite: changing the residual list along an
  -- equality `r : rest ≡ rest'` transports the box-of by `subst₂` over the
  -- `cong (einL ++_)` / `cong (eoutL ++_)` endpoints.  (`refl` on `r`.)
  box-rest-rewrite
    : ∀ (einL eoutL : List X) {rest rest' : List X} (r : rest ≡ rest')
        (g : FlatGen einL eoutL)
    → subst₂ HomTerm
        (cong unflatten (cong (einL  ++_) r))
        (cong unflatten (cong (eoutL ++_) r))
        (box-of einL eoutL rest g)
      ≡ box-of einL eoutL rest' g
  box-rest-rewrite einL eoutL refl g = refl

  -- The constant K-suffix object (the `id`-carried far block).
  RsufObj : (ys : List (Fin K.nV)) → ObjTerm
  RsufObj ys = unflatten (map C.vlab (map injR ys))

  pe-stackG : List (Fin G.nE) → List (Fin G.nV) → List (Fin G.nV)
  pe-stackG o s = proj₁ (process-edges G o s)

  -- Pure-L stack agreement (from the gate's `proc-stack-emb`, φ = injL).
  proc-stack-emb-L
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → pe-stackC (map (_↑ˡ K.nE) es) (map injL xs)
      ≡ map injL (pe-stackG es xs)
  proc-stack-emb-L es xs = TG.proc-stack-emb es xs

  -- The pure-L inner term, with its codomain transported from
  -- `pe-stackC (map ψG es) (map injL xs)` to `map injL (pe-stackG es xs)`.
  Lterm
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → HomTerm (unflatten (map C.vlab (map injL xs)))
              (unflatten (map C.vlab (map injL (pe-stackG es xs))))
  Lterm es xs =
    coeC {map injL xs} (proc-stack-emb-L es xs)
         (pe-termC (map (_↑ˡ K.nE) es) (map injL xs))

  -- The G-side factorization statement, framed by `BTC.uf++`.
  GFactored
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injL xs ++ map injR ys)))
              (unflatten (map C.vlab (map injL (pe-stackG es xs) ++ map injR ys)))
  GFactored es xs ys =
    _≅_.to (BTC.uf++ (map injL (pe-stackG es xs)) (map injR ys))
    ∘ (Lterm es xs ⊗₁ id {RsufObj ys})
    ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))

  -- The mixed-stack agreement (from `process-edges-↑ˡ-on-mixed`).
  mixed-stack-G
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → pe-stackC (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys)
      ≡ map injL (pe-stackG es xs) ++ map injR ys
  mixed-stack-G es xs ys =
    cong proj₁ (proj₂ (process-edges-↑ˡ-on-mixed G K es xs ys))

  ------------------------------------------------------------------------
  -- ### Reusable per-edge pieces for the G-suffix induction.

  -- UIP on the vertex-list type (`--with-K`).
  uipL : ∀ {a b : List (Fin C.nV)} (p q : a ≡ b) → p ≡ q
  uipL refl refl = refl

  pvlC : {xs ys : List (Fin C.nV)} → xs Perm.↭ ys
       → HomTerm (unflatten (map C.vlab xs)) (unflatten (map C.vlab ys))
  pvlC = BTC.pvl

  -- `permute-via-vlab` of the identity permutation is `id` (definitional:
  -- `map⁺ vlab refl = refl` and `permute refl = id`).
  pvl-refl : ∀ {xs : List (Fin C.nV)} → pvlC (Perm.↭-refl {x = xs}) ≈Term id
  pvl-refl = ≈-Term-refl

  -- `id` factors through the `uf++` framing as `id ⊗₁ id`.
  id-as-tensor
    : ∀ (As Bs : List (Fin C.nV))
    → id {unflatten (map C.vlab (As ++ Bs))}
      ≈Term _≅_.to (BTC.uf++ As Bs)
            ∘ (id {unflatten (map C.vlab As)} ⊗₁ id {unflatten (map C.vlab Bs)})
            ∘ _≅_.from (BTC.uf++ As Bs)
  id-as-tensor As Bs = begin
    id
      ≈⟨ ≈-Term-sym (_≅_.isoˡ (BTC.uf++ As Bs)) ⟩
    _≅_.to (BTC.uf++ As Bs) ∘ _≅_.from (BTC.uf++ As Bs)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym idˡ ⟩
    _≅_.to (BTC.uf++ As Bs) ∘ id ∘ _≅_.from (BTC.uf++ As Bs)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym id⊗id≈id ⟩∘⟨refl ⟩
    _≅_.to (BTC.uf++ As Bs) ∘ (id ⊗₁ id) ∘ _≅_.from (BTC.uf++ As Bs) ∎

  ------------------------------------------------------------------------
  -- ### `head-factor` — the NON-INDUCTIVE single-G-edge FIRE factorization.
  --
  -- A single FIRE G-edge fired from the mixed stack factors, modulo the
  -- `BTC.uf++` framing, as `(L-head ⊗₁ id)` on the untouched `map injR ys`
  -- suffix.  `L-head` is the pure-injL FIRE head: the `box-of` on the
  -- `map injL`-prefix residual composed with the front-permute `pvlC p`.
  --
  -- Stated on the BUILDING BLOCKS (`box-of` on the `map C.vlab ∘ map injL/
  -- injR` images + `pvlC`), GENERIC in the generator `g` — so the cons step
  -- (separately) connects the actual `fire-mid C (ψG e)` / computed perm to
  -- this form via the `ein-c`/`eout-c`-reductions + the eval residual.
  --
  --   box-of eiL eoL (rgL ++ Rys) g  ∘  pvlC (++⁺ p ↭-refl)
  --     ≈ to(uf++ (eoL'·) Rys)
  --       ∘ ((box-of eiL eoL rgL g ∘ pvlC p) ⊗₁ id {U Rys})
  --       ∘ from(uf++ (eiL'·) Rys)
  --
  -- where the framing lists are at the `injL`-prefix / `injR`-suffix split.
  -- The box part is `BoxAssoc.box-suffix` (+ `box-rest-rewrite` to split the
  -- `map C.vlab` residual into `rgL ++ Rys`); the permute part is the
  -- COROLLARY of `BlockTensor.pvv-block-tensor` at `q = ↭-refl` (+ `pvl-refl`).

  -- The `box-of` factor lives at the `map C.vlab ∘ map injL/injR` level.
  -- `vc∘L` / `vc∘R` are the C-label images of the `injL`/`injR` blocks.
  vc∘L : List (Fin G.nV) → List X
  vc∘L xs = map C.vlab (map injL xs)

  vc∘R : List (Fin K.nV) → List X
  vc∘R ys = map C.vlab (map injR ys)

  -- The permute factor: `pvlC (++⁺ p ↭-refl)` slides past `BTC.uf++` as
  -- `(pvlC p ⊗₁ id)` (corollary of `pvv-block-tensor`@refl + `pvl-refl`).
  head-perm-factor
    : ∀ {as bs : List (Fin C.nV)} (p : as Perm.↭ bs) (Rs : List (Fin C.nV))
    → pvlC (PermProp.++⁺ p (Perm.↭-refl {x = Rs}))
      ≈Term _≅_.to (BTC.uf++ bs Rs)
            ∘ (pvlC p ⊗₁ id {unflatten (map C.vlab Rs)})
            ∘ _≅_.from (BTC.uf++ as Rs)
  head-perm-factor {as} {bs} p Rs = begin
    pvlC (PermProp.++⁺ p (Perm.↭-refl {x = Rs}))
      ≈⟨ BTC.pvv-block-tensor p (Perm.↭-refl {x = Rs}) ⟩
    _≅_.to (BTC.uf++ bs Rs) ∘ (pvlC p ⊗₁ pvlC (Perm.↭-refl {x = Rs}))
      ∘ _≅_.from (BTC.uf++ as Rs)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl pvl-refl ⟩∘⟨refl ⟩
    _≅_.to (BTC.uf++ bs Rs) ∘ (pvlC p ⊗₁ id {unflatten (map C.vlab Rs)})
      ∘ _≅_.from (BTC.uf++ as Rs) ∎

  ------------------------------------------------------------------------
  -- ### `box-suffix-BTC` — `box-suffix` reframed into the `BTC.uf++`
  -- convention (the framing `head-perm-factor` / `pvv-block-tensor` use).
  --
  -- `box-suffix` is raw-`unflatten-++-≅`-framed on `List X`; we lift it to
  -- `BTC.uf++ · ·` on `List (Fin C.nV)` blocks `Lblk`/`Rblk`, bridging the
  -- two `map-++ C.vlab` reconciliations (the block-1 `map C.vlab (Lblk ++
  -- restL)` vs `map C.vlab Lblk ++ map C.vlab restL`, and the `BTC.uf++`
  -- internal `sym (map-++ C.vlab (Lblk ++ restL) Rblk)`) via
  -- `BNB.to-subst₂-≅`/`from-subst₂-≅`.

  -- to/from of `BTC.uf++ As Bs` in terms of the raw `unflatten-++-≅`.
  private
    to-BTC : ∀ (As Bs : List (Fin C.nV))
           → _≅_.to (BTC.uf++ As Bs)
             ≡ subst₂ HomTerm refl (cong unflatten (sym (map-++ C.vlab As Bs)))
                 (_≅_.to (unflatten-++-≅ (map C.vlab As) (map C.vlab Bs)))
    to-BTC As Bs = BNB.to-subst₂-≅ (cong unflatten (sym (map-++ C.vlab As Bs)))
                     (unflatten-++-≅ (map C.vlab As) (map C.vlab Bs))

    from-BTC : ∀ (As Bs : List (Fin C.nV))
             → _≅_.from (BTC.uf++ As Bs)
               ≡ subst₂ HomTerm (cong unflatten (sym (map-++ C.vlab As Bs))) refl
                   (_≅_.from (unflatten-++-≅ (map C.vlab As) (map C.vlab Bs)))
    from-BTC As Bs = BNB.from-subst₂-≅ (cong unflatten (sym (map-++ C.vlab As Bs)))
                       (unflatten-++-≅ (map C.vlab As) (map C.vlab Bs))

  private
    Rys-flat : (ys : List (Fin K.nV)) → List X
    Rys-flat ys = map C.vlab (map injR ys)

  -- `box-suffix` reframed into the `BTC.uf++` convention.  `eiBlk`/`eoBlk`
  -- are the (whole) box endpoint blocks, `rgBlk` the residual prefix, `ys`
  -- the untouched K-suffix; `g` the generator at the C-label endpoints.
  -- The LHS is `box-suffix`'s `(++-assoc)`-substituted box on the SPLIT
  -- residual `map C.vlab rgBlk ++ Rys`; the RHS is BTC-framed on the
  -- WHOLE block lists `eoBlk ++ rgBlk` / `eiBlk ++ rgBlk`, with the box
  -- endpoints transported across the `map-++ C.vlab` block-1 split.
  -- The combined `box-of`-domain/codomain transports `eiBlk-img++(rgBlk-img
  -- ++Rys) ≡ map C.vlab ((eiBlk++rgBlk)++map injR ys)` (the `++-assoc` plus
  -- the two `map-++ C.vlab` layers), one per box endpoint block.
  private
    whole-eq : ∀ (lBlk rgBlk : List (Fin C.nV)) (ys : List (Fin K.nV))
             → map C.vlab lBlk ++ (map C.vlab rgBlk ++ Rys-flat ys)
               ≡ map C.vlab ((lBlk ++ rgBlk) ++ map injR ys)
    whole-eq lBlk rgBlk ys =
      trans (sym (++-assoc (map C.vlab lBlk) (map C.vlab rgBlk) (Rys-flat ys)))
      (trans (cong (_++ Rys-flat ys) (sym (map-++ C.vlab lBlk rgBlk)))
             (sym (map-++ C.vlab (lBlk ++ rgBlk) (map injR ys))))

  box-suffix-BTC
    : ∀ (eiBlk eoBlk rgBlk : List (Fin C.nV)) (ys : List (Fin K.nV))
        (g : FlatGen (map C.vlab eiBlk) (map C.vlab eoBlk))
    → subst₂ HomTerm
        (cong unflatten (whole-eq eiBlk rgBlk ys))
        (cong unflatten (whole-eq eoBlk rgBlk ys))
        (box-of (map C.vlab eiBlk) (map C.vlab eoBlk)
                (map C.vlab rgBlk ++ Rys-flat ys) g)
      ≈Term _≅_.to (BTC.uf++ (eoBlk ++ rgBlk) (map injR ys))
            ∘ (subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                 (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
                 ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys))
  -- The `BTC`-framing box-suffix is the generic `BlockBoxSuffix C.vlab`
  -- reframe at `Rblk = map injR ys` (`Rys-flat ys = map C.vlab (map injR ys)`
  -- and `RsufObj ys = BBSC.BT.R-obj (map injR ys)` definitionally; the local
  -- `whole-eq · · ys` agrees with `BBSC`'s `whole-eq · · (map injR ys)`).
  box-suffix-BTC eiBlk eoBlk rgBlk ys g =
    BBSC.box-suffix-framed eiBlk eoBlk rgBlk (map injR ys) g

  ------------------------------------------------------------------------
  -- ### `head-factor` — the single-G-edge FIRE head-step factorization.
  --
  -- THE per-edge piece (NON-inductive).  A single FIRE G-edge fired from
  -- the mixed stack — its `box-of` (on the `injL`-prefix residual `rgL`,
  -- in `box-suffix`'s `(++-assoc)`-substituted form) precomposed with the
  -- front-permute `pvlC (++⁺ p ↭-refl)` — factors, modulo the `BTC.uf++`
  -- framing on the WHOLE `injL`-block lists, as `(L-head ⊗₁ id)` on the
  -- untouched `map injR ys` suffix, where
  --
  --   L-head = (box on the `injL`-prefix residual) ∘ pvlC p
  --
  -- is the pure-injL FIRE head.  Box half = `box-suffix-BTC`; permute half
  -- = `head-perm-factor` (= `pvv-block-tensor`@↭-refl + `pvl-refl`); combine
  -- = middle `from(BTC eirg) ∘ to(BTC eirg) = id` cancellation + `⊗-∘-dist`.
  -- The cons step (`gblock-factor`, separate) reconciles the actual
  -- `fire-mid C (ψG e)` / computed extract-prefix perm to this `box`/`++⁺ p
  -- ↭-refl` form via the `ein-c`/`eout-c` reductions + the eval residual.
  head-factor
    : ∀ (eiBlk eoBlk rgBlk : List (Fin C.nV)) (xs : List (Fin G.nV))
        (ys : List (Fin K.nV))
        (g : FlatGen (map C.vlab eiBlk) (map C.vlab eoBlk))
        (p : map injL xs Perm.↭ eiBlk ++ rgBlk)
    → subst₂ HomTerm
        (cong unflatten (whole-eq eiBlk rgBlk ys))
        (cong unflatten (whole-eq eoBlk rgBlk ys))
        (box-of (map C.vlab eiBlk) (map C.vlab eoBlk)
                (map C.vlab rgBlk ++ Rys-flat ys) g)
      ∘ pvlC (PermProp.++⁺ p (Perm.↭-refl {x = map injR ys}))
      ≈Term _≅_.to (BTC.uf++ (eoBlk ++ rgBlk) (map injR ys))
            ∘ ((subst₂ HomTerm
                  (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                  (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                  (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
                ∘ pvlC p) ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
  head-factor eiBlk eoBlk rgBlk xs ys g p = begin
      Box ∘ pvlC (PermProp.++⁺ p (Perm.↭-refl {x = map injR ys}))
        ≈⟨ ∘-resp-≈ (box-suffix-BTC eiBlk eoBlk rgBlk ys g)
                    (head-perm-factor p (map injR ys)) ⟩
      (to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ from-eirg)
        ∘ (to-eirg ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs)
        ≈⟨ cancel-mid ⟩
      to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      to-eorg ∘ ((BoxSub ⊗₁ id {RsufObj ys}) ∘ (pvlC p ⊗₁ id {RsufObj ys})) ∘ from-xs
        ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
      to-eorg ∘ ((BoxSub ∘ pvlC p) ⊗₁ (id {RsufObj ys} ∘ id {RsufObj ys})) ∘ from-xs
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩∘⟨refl ⟩
      to-eorg ∘ ((BoxSub ∘ pvlC p) ⊗₁ id {RsufObj ys}) ∘ from-xs ∎
    where
      Box = subst₂ HomTerm
              (cong unflatten (whole-eq eiBlk rgBlk ys))
              (cong unflatten (whole-eq eoBlk rgBlk ys))
              (box-of (map C.vlab eiBlk) (map C.vlab eoBlk)
                      (map C.vlab rgBlk ++ Rys-flat ys) g)
      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                 (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
      to-eorg = _≅_.to   (BTC.uf++ (eoBlk ++ rgBlk) (map injR ys))
      from-eirg = _≅_.from (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys))
      to-eirg = _≅_.to   (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys))
      from-xs = _≅_.from (BTC.uf++ (map injL xs) (map injR ys))

      cancel-mid
        : (to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ from-eirg)
            ∘ (to-eirg ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs)
          ≈Term to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys})
                  ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs
      cancel-mid =
        cancel-mid-iso to-eorg (BoxSub ⊗₁ id {RsufObj ys}) from-eirg
          to-eirg (pvlC p ⊗₁ id {RsufObj ys}) from-xs
          (_≅_.isoʳ (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys)))

  ------------------------------------------------------------------------
  -- ### `head-factor-K` — the K-side single-edge FIRE factorization
  -- (the K-side mirror of `head-factor`, with the carried G-output PREFIX).
  --
  -- For a single FIRE K-edge fired from the mixed stack `map injL P ++ map
  -- injR ys` (the `map injL P` is the carried G-output PREFIX held by `id`),
  -- the head term factors — modulo `BTC.uf++` framing — as `(id {prefix} ⊗₁
  -- K-head)`, where `K-head = (box on the injR-block residual) ∘ pvlC q` is
  -- the pure-injR FIRE head.  Mirror of `head-factor` with LEFT/RIGHT swapped:
  -- the carried block is the LEFT prefix `map injL P` (held by `id`), the box
  -- acts on the RIGHT injR-block `eiBlk ++ rgBlk`.
  --
  -- Box half = `box-prefix-BTC` (`box-prefix` reframed into `BTC.uf++`);
  -- permute half = `head-perm-factor-K` (= `pvv-block-tensor`@(p=↭-refl) +
  -- `pvl-refl`); combine = middle `from(BTC) ∘ to(BTC) = id` cancellation +
  -- `⊗-∘-dist`.

  -- The constant G-prefix object (the `id`-carried near block).
  RpreObj : (P : List (Fin G.nV)) → ObjTerm
  RpreObj P = unflatten (map C.vlab (map injL P))

  -- The permute factor: `pvlC (++⁺ ↭-refl q)` slides past `BTC.uf++` as
  -- `(id ⊗₁ pvlC q)` (corollary of `pvv-block-tensor`@(p=↭-refl) + `pvl-refl`).
  -- Mirror of `head-perm-factor` (identity on the LEFT prefix `Ls`).
  head-perm-factor-K
    : ∀ (Ls : List (Fin C.nV)) {as bs : List (Fin C.nV)} (q : as Perm.↭ bs)
    → pvlC (PermProp.++⁺ (Perm.↭-refl {x = Ls}) q)
      ≈Term _≅_.to (BTC.uf++ Ls bs)
            ∘ (id {unflatten (map C.vlab Ls)} ⊗₁ pvlC q)
            ∘ _≅_.from (BTC.uf++ Ls as)
  head-perm-factor-K Ls {as} {bs} q = begin
    pvlC (PermProp.++⁺ (Perm.↭-refl {x = Ls}) q)
      ≈⟨ BTC.pvv-block-tensor (Perm.↭-refl {x = Ls}) q ⟩
    _≅_.to (BTC.uf++ Ls bs) ∘ (pvlC (Perm.↭-refl {x = Ls}) ⊗₁ pvlC q)
      ∘ _≅_.from (BTC.uf++ Ls as)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ pvl-refl ≈-Term-refl ⟩∘⟨refl ⟩
    _≅_.to (BTC.uf++ Ls bs) ∘ (id {unflatten (map C.vlab Ls)} ⊗₁ pvlC q)
      ∘ _≅_.from (BTC.uf++ Ls as) ∎

  ------------------------------------------------------------------------
  -- ### `box-prefix-BTC` — `box-prefix`'s LHS shape reframed into `BTC.uf++`.
  --
  -- The K-side box-part: a `box-prefix`-LHS-shaped box (the carried injL
  -- prefix `map injL P` held by `id`, the K-edge box `box-of eiBlk eoBlk
  -- rgBlk` acting on the injR block) lifted from raw `unflatten-++-≅` into the
  -- `BTC.uf++` convention.  No `++-assoc`: the prefix structure `P ++ (eiBlk
  -- ++ rgBlk)` already matches, so only the two `map-++ C.vlab` (block-2 and
  -- the outer) reconciliations are needed.  `BoxSub` is the SAME pure-injR
  -- per-edge box `head-factor` uses (`box-of` on the `map C.vlab`-block lists).

  -- The combined `box-of`-endpoint transports `P-img ++ (eiBlk-img ++
  -- rgBlk-img) ≡ map C.vlab (map injL P ++ (eiBlk ++ rgBlk))` — the inner
  -- `map-++ C.vlab eiBlk rgBlk` (block-2 split) plus the outer `map-++
  -- C.vlab (map injL P) (eiBlk ++ rgBlk)`, one per box endpoint block.
  private
    Pimg : (P : List (Fin G.nV)) → List X
    Pimg P = map C.vlab (map injL P)

    whole-eq-K : ∀ (P : List (Fin G.nV)) (eBlk rgBlk : List (Fin C.nV))
               → Pimg P ++ (map C.vlab eBlk ++ map C.vlab rgBlk)
                 ≡ map C.vlab (map injL P ++ (eBlk ++ rgBlk))
    whole-eq-K P eBlk rgBlk =
      trans (cong (Pimg P ++_) (sym (map-++ C.vlab eBlk rgBlk)))
            (sym (map-++ C.vlab (map injL P) (eBlk ++ rgBlk)))

  -- to/from of `unflatten-++-≅ L R` under a BLOCK-2 list equality `r : R ≡ R'`
  -- (the `map-++ C.vlab` split on the box block), a single `subst` over R.
  -- (Mirror of `to-blk1`/`from-blk1`, on the SECOND block.)
  private
    to-blk2 : ∀ (L R R' : List X) (r : R ≡ R')
            → subst (λ z → HomTerm (unflatten L ⊗₀ unflatten z) (unflatten (L ++ z)))
                    r (_≅_.to (unflatten-++-≅ L R))
              ≡ _≅_.to (unflatten-++-≅ L R')
    to-blk2 L R .R refl = refl

    from-blk2 : ∀ (L R R' : List X) (r : R ≡ R')
              → subst (λ z → HomTerm (unflatten (L ++ z)) (unflatten L ⊗₀ unflatten z))
                      r (_≅_.from (unflatten-++-≅ L R))
                ≡ _≅_.from (unflatten-++-≅ L R')
    from-blk2 L R .R refl = refl

  ------------------------------------------------------------------------
  -- `box-prefix`'s LHS shape (the carried injL prefix `map injL P` held by
  -- `id`, the K-edge box on the injR block `eiBlk ++ rgBlk`) reframed into
  -- `BTC.uf++`.  `BoxSub` is the SAME pure-injR per-edge box `head-factor`
  -- uses.
  box-prefix-BTC
    : ∀ (P : List (Fin G.nV)) (eiBlk eoBlk rgBlk : List (Fin C.nV))
        (g : FlatGen (map C.vlab eiBlk) (map C.vlab eoBlk))
    → subst₂ HomTerm
        (cong unflatten (whole-eq-K P eiBlk rgBlk))
        (cong unflatten (whole-eq-K P eoBlk rgBlk))
        (_≅_.to (unflatten-++-≅ (Pimg P) (map C.vlab eoBlk ++ map C.vlab rgBlk))
         ∘ (id {RpreObj P}
            ⊗₁ box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
         ∘ _≅_.from (unflatten-++-≅ (Pimg P) (map C.vlab eiBlk ++ map C.vlab rgBlk)))
      ≈Term _≅_.to (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
            ∘ (id {RpreObj P}
               ⊗₁ subst₂ HomTerm
                    (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                    (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                    (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g))
            ∘ _≅_.from (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
  box-prefix-BTC P eiBlk eoBlk rgBlk g = ≈-Term-sym (≡⇒≈Term rhs-≡)
    where
      P'  = Pimg P
      eiL = map C.vlab eiBlk
      eoL = map C.vlab eoBlk
      rgL = map C.vlab rgBlk
      UP  = RpreObj P

      boxRg = box-of eiL eoL rgL g

      -- the two `map-++ C.vlab` block-2 splits.
      mpei = sym (map-++ C.vlab eiBlk rgBlk)   -- map C.vlab (eiBlk++rgBlk) ≡ eiL ++ rgL  (reversed)
      mpeo = sym (map-++ C.vlab eoBlk rgBlk)

      -- the outer `BTC.uf++` splits.
      Cei = sym (map-++ C.vlab (map injL P) (eiBlk ++ rgBlk))
      Ceo = sym (map-++ C.vlab (map injL P) (eoBlk ++ rgBlk))

      to-raw = _≅_.to   (unflatten-++-≅ P' (eoL ++ rgL))
      fr-raw = _≅_.from (unflatten-++-≅ P' (eiL ++ rgL))
      M      = id {UP} ⊗₁ boxRg
      BoxSub = subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg

      -- `id_UP ⊗ subst₂ … box`-subst push (subst on the SECOND ⊗-factor).
      ⊗-push
        : ∀ {a₁ a₂ b₁ b₂ : List X} (r₁ : a₁ ≡ a₂) (r₂ : b₁ ≡ b₂)
            (f : HomTerm (unflatten a₁) (unflatten b₁))
        → id {UP} ⊗₁ (subst₂ HomTerm (cong unflatten r₁) (cong unflatten r₂) f)
          ≡ subst₂ HomTerm
              (cong (λ z → UP ⊗₀ unflatten z) r₁)
              (cong (λ z → UP ⊗₀ unflatten z) r₂)
              (id {UP} ⊗₁ f)
      ⊗-push refl refl f = refl

      -- A `subst` over a 2-place `HomTerm` motive as a `subst₂`.
      subst-2 : ∀ {a b : List X} (f h : List X → ObjTerm) (r : a ≡ b)
                  (t : HomTerm (f a) (h a))
              → subst (λ z → HomTerm (f z) (h z)) r t
                ≡ subst₂ HomTerm (cong f r) (cong h r) t
      subst-2 f h refl t = refl

      -- to/from(BTC) re-expressed on the SPLIT raw blocks (to-BTC/from-BTC +
      -- the blk2 `map-++ C.vlab` reconciliation, recast via `subst-2`),
      -- combined to a single `subst₂` via `subst₂-HomTerm-∘`.  (Mirror of
      -- `box-suffix-BTC`'s `to-eo-≡`/`from-ei-≡`, on the SECOND block.)
      to-eo-≡ :
        _≅_.to (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
        ≡ subst₂ HomTerm
            (trans (cong (λ z → UP ⊗₀ unflatten z) mpeo) refl)
            (trans (cong (λ z → unflatten (P' ++ z)) mpeo) (cong unflatten Ceo))
            to-raw
      to-eo-≡ =
        trans (to-BTC (map injL P) (eoBlk ++ rgBlk))
        (trans (cong (subst₂ HomTerm refl (cong unflatten Ceo))
                     (trans (sym (to-blk2 P' (eoL ++ rgL) (map C.vlab (eoBlk ++ rgBlk)) mpeo))
                            (subst-2 (λ z → UP ⊗₀ unflatten z) (λ z → unflatten (P' ++ z))
                               mpeo to-raw)))
               (subst₂-HomTerm-∘
                  (cong (λ z → UP ⊗₀ unflatten z) mpeo) refl
                  (cong (λ z → unflatten (P' ++ z)) mpeo) (cong unflatten Ceo)
                  to-raw))

      from-ei-≡ :
        _≅_.from (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
        ≡ subst₂ HomTerm
            (trans (cong (λ z → unflatten (P' ++ z)) mpei) (cong unflatten Cei))
            (trans (cong (λ z → UP ⊗₀ unflatten z) mpei) refl)
            fr-raw
      from-ei-≡ =
        trans (from-BTC (map injL P) (eiBlk ++ rgBlk))
        (trans (cong (subst₂ HomTerm (cong unflatten Cei) refl)
                     (trans (sym (from-blk2 P' (eiL ++ rgL) (map C.vlab (eiBlk ++ rgBlk)) mpei))
                            (subst-2 (λ z → unflatten (P' ++ z)) (λ z → UP ⊗₀ unflatten z)
                               mpei fr-raw)))
               (subst₂-HomTerm-∘
                  (cong (λ z → unflatten (P' ++ z)) mpei) (cong unflatten Cei)
                  (cong (λ z → UP ⊗₀ unflatten z) mpei) refl
                  fr-raw))

      Qto = trans (cong (λ z → UP ⊗₀ unflatten z) mpeo) refl   -- to-eo-≡ dom
      Qfr = trans (cong (λ z → UP ⊗₀ unflatten z) mpei) refl   -- from-ei-≡ cod
      B'i = cong (λ z → unflatten (P' ++ z)) mpei
      B'o = cong (λ z → unflatten (P' ++ z)) mpeo
      Pp  = trans B'i (cong unflatten Cei)
      Rc  = trans B'o (cong unflatten Ceo)

      -- the middle box factor matches `subst₂ Qfr Qto M` modulo the two
      -- `trans _ refl` pads (`trans-reflʳ`).
      mid-≡ : id {UP} ⊗₁ BoxSub ≡ subst₂ HomTerm Qfr Qto M
      mid-≡ =
        trans (⊗-push mpei mpeo boxRg)
              (cong₂ (λ p q → subst₂ HomTerm p q M)
                     (sym (trans-reflʳ (cong (λ z → UP ⊗₀ unflatten z) mpei)))
                     (sym (trans-reflʳ (cong (λ z → UP ⊗₀ unflatten z) mpeo))))

      -- `B'·` ≡ `cong unflatten (cong (P' ++_) mp·)` (the `cong-∘` bridge).
      Aei = cong (P' ++_) mpei
      Aeo = cong (P' ++_) mpeo

      rhs-≡ :
        _≅_.to (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
          ∘ (id {UP} ⊗₁ BoxSub)
          ∘ _≅_.from (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
        ≡ subst₂ HomTerm
            (cong unflatten (whole-eq-K P eiBlk rgBlk))
            (cong unflatten (whole-eq-K P eoBlk rgBlk))
            (to-raw ∘ M ∘ fr-raw)
      rhs-≡ = ≡R.begin
          _≅_.to (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
            ∘ (id {UP} ⊗₁ BoxSub)
            ∘ _≅_.from (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
            -- Step 1: rewrite the three BTC factors to substituted raw.
            ≡R.≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) to-eo-≡ mid-≡ from-ei-≡ ⟩
          subst₂ HomTerm Qto Rc to-raw
            ∘ subst₂ HomTerm Qfr Qto M
            ∘ subst₂ HomTerm Pp Qfr fr-raw
            -- Step 2: recombine the M / from factors.
            ≡R.≡⟨ cong (λ w → subst₂ HomTerm Qto Rc to-raw ∘ w)
                    (sym (subst₂-HomTerm-∘-dist Pp Qfr Qto M fr-raw)) ⟩
          subst₂ HomTerm Qto Rc to-raw
            ∘ subst₂ HomTerm Pp Qto (M ∘ fr-raw)
            -- Step 3: recombine the to factor.
            ≡R.≡⟨ sym (subst₂-HomTerm-∘-dist Pp Qto Rc to-raw (M ∘ fr-raw)) ⟩
          subst₂ HomTerm Pp Rc (to-raw ∘ M ∘ fr-raw)
            -- Step 4: re-nest the combined `subst₂` into `Cei'∘B'·` form.
            ≡R.≡⟨ sym (subst₂-HomTerm-∘
                      B'i (cong unflatten Cei)
                      B'o (cong unflatten Ceo)
                      (to-raw ∘ M ∘ fr-raw)) ⟩
          subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
            (subst₂ HomTerm B'i B'o (to-raw ∘ M ∘ fr-raw))
            -- Step 5: `B'·` ≡ `cong unflatten (cong (P' ++_) mp·)`.
            ≡R.≡⟨ cong (λ p → subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo) p)
                    (cong₂ (λ a b → subst₂ HomTerm a b (to-raw ∘ M ∘ fr-raw))
                           (cong-∘ mpei) (cong-∘ mpeo)) ⟩
          subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
            (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
               (to-raw ∘ M ∘ fr-raw))
            -- Step 6: fold the two layers into the single `whole-eq-K` subst.
            ≡R.≡⟨ fold-whole ⟩
          subst₂ HomTerm
            (cong unflatten (whole-eq-K P eiBlk rgBlk))
            (cong unflatten (whole-eq-K P eoBlk rgBlk))
            (to-raw ∘ M ∘ fr-raw) ≡R.∎
        where
          module ≡R = ≡-Reasoning
          cong₃ : ∀ {a} {A B C D : Set a} (f : A → B → C → D)
                    {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z'
                  → f x y z ≡ f x' y' z'
          cong₃ f refl refl refl = refl

          fold-whole :
            subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
              (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
                 (to-raw ∘ M ∘ fr-raw))
            ≡ subst₂ HomTerm
                (cong unflatten (whole-eq-K P eiBlk rgBlk))
                (cong unflatten (whole-eq-K P eoBlk rgBlk))
                (to-raw ∘ M ∘ fr-raw)
          fold-whole =
            trans
              (subst₂-HomTerm-∘
                 (cong unflatten Aei) (cong unflatten Cei)
                 (cong unflatten Aeo) (cong unflatten Ceo)
                 (to-raw ∘ M ∘ fr-raw))
              (cong₂ (λ p q → subst₂ HomTerm p q (to-raw ∘ M ∘ fr-raw))
                     (sym (cong-whole eiBlk)) (sym (cong-whole eoBlk)))
            where
              cong-whole : ∀ (eBlk : List (Fin C.nV))
                         → cong unflatten (whole-eq-K P eBlk rgBlk)
                           ≡ trans (cong unflatten (cong (P' ++_) (sym (map-++ C.vlab eBlk rgBlk))))
                                   (cong unflatten (sym (map-++ C.vlab (map injL P) (eBlk ++ rgBlk))))
              cong-whole eBlk =
                sym (trans-cong {f = unflatten}
                       (cong (P' ++_) (sym (map-++ C.vlab eBlk rgBlk))))

  ------------------------------------------------------------------------
  -- ### `head-factor-K` — the single-K-edge FIRE head-step factorization.
  --
  -- THE per-edge K-side piece (NON-inductive), the mirror of `head-factor`.
  -- A single FIRE K-edge fired from the mixed stack `map injL P ++ map injR
  -- ys` — its `box-prefix`-LHS-shaped box (carried `map injL P` prefix held
  -- by `id`, the K-edge `box-of` on the injR-block residual `rgBlk`, in
  -- `whole-eq-K`-substituted form) precomposed with the front-permute
  -- `pvlC (++⁺ ↭-refl q)` (identity on the LEFT `map injL P` prefix) —
  -- factors, modulo the `BTC.uf++` framing on the WHOLE block lists, as
  -- `(id {prefix} ⊗₁ K-head)` on the carried `map injL P` prefix, where
  --
  --   K-head = (box on the injR-block residual) ∘ pvlC q
  --
  -- is the pure-injR FIRE head.  Box half = `box-prefix-BTC`; permute half =
  -- `head-perm-factor-K` (= `pvv-block-tensor`@(p=↭-refl) + `pvl-refl`);
  -- combine = middle `from(BTC) ∘ to(BTC) = id` cancellation + `⊗-∘-dist`.
  -- The cons step (`kblock-factor`, separate) reconciles the actual
  -- `fire-mid C (ψK e)` / computed extract-prefix perm to this `box`/`++⁺
  -- ↭-refl q` form via the `ein-c`/`eout-c` reductions + the keystone (K
  -- prepends its eout to the stack front, so the post-edge stack only `↭`s).
  head-factor-K
    : ∀ (P : List (Fin G.nV)) (eiBlk eoBlk rgBlk : List (Fin C.nV))
        (ys : List (Fin K.nV))
        (g : FlatGen (map C.vlab eiBlk) (map C.vlab eoBlk))
        (q : map injR ys Perm.↭ eiBlk ++ rgBlk)
    → subst₂ HomTerm
        (cong unflatten (whole-eq-K P eiBlk rgBlk))
        (cong unflatten (whole-eq-K P eoBlk rgBlk))
        (_≅_.to (unflatten-++-≅ (Pimg P) (map C.vlab eoBlk ++ map C.vlab rgBlk))
         ∘ (id {RpreObj P}
            ⊗₁ box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
         ∘ _≅_.from (unflatten-++-≅ (Pimg P) (map C.vlab eiBlk ++ map C.vlab rgBlk)))
      ∘ pvlC (PermProp.++⁺ (Perm.↭-refl {x = map injL P}) q)
      ≈Term _≅_.to (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
            ∘ (id {RpreObj P}
               ⊗₁ (subst₂ HomTerm
                     (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                     (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                     (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
                  ∘ pvlC q))
            ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))
  head-factor-K P eiBlk eoBlk rgBlk ys g q = begin
      Box-sub ∘ pvlC (PermProp.++⁺ (Perm.↭-refl {x = map injL P}) q)
        ≈⟨ ∘-resp-≈ (box-prefix-BTC P eiBlk eoBlk rgBlk g)
                    (head-perm-factor-K (map injL P) q) ⟩
      (to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
        ∘ (to-eirg ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys)
        ≈⟨ cancel-mid ⟩
      to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      to-eorg ∘ ((id {RpreObj P} ⊗₁ BoxSub) ∘ (id {RpreObj P} ⊗₁ pvlC q)) ∘ from-ys
        ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
      to-eorg ∘ ((id {RpreObj P} ∘ id {RpreObj P}) ⊗₁ (BoxSub ∘ pvlC q)) ∘ from-ys
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩∘⟨refl ⟩
      to-eorg ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC q)) ∘ from-ys ∎
    where
      Box = _≅_.to (unflatten-++-≅ (Pimg P) (map C.vlab eoBlk ++ map C.vlab rgBlk))
            ∘ (id {RpreObj P}
               ⊗₁ box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
            ∘ _≅_.from (unflatten-++-≅ (Pimg P) (map C.vlab eiBlk ++ map C.vlab rgBlk))
      Box-sub = subst₂ HomTerm
                  (cong unflatten (whole-eq-K P eiBlk rgBlk))
                  (cong unflatten (whole-eq-K P eoBlk rgBlk))
                  Box
      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                 (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g)
      to-eorg = _≅_.to   (BTC.uf++ (map injL P) (eoBlk ++ rgBlk))
      from-eirg = _≅_.from (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
      to-eirg = _≅_.to   (BTC.uf++ (map injL P) (eiBlk ++ rgBlk))
      from-ys = _≅_.from (BTC.uf++ (map injL P) (map injR ys))

      cancel-mid
        : (to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
            ∘ (to-eirg ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys)
          ≈Term to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub)
                  ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys
      cancel-mid =
        cancel-mid-iso to-eorg (id {RpreObj P} ⊗₁ BoxSub) from-eirg
          to-eirg (id {RpreObj P} ⊗₁ pvlC q) from-ys
          (_≅_.isoʳ (BTC.uf++ (map injL P) (eiBlk ++ rgBlk)))

  ------------------------------------------------------------------------
  -- ### `gblock-factor` — the G-side suffix-carry factorization.
  --
  -- Statement (with the SOUND `Reservoir≤1` freshness hypothesis, threaded
  -- exactly like `StackEquivariance.process-edges-equivariant`):
  --   Reservoir≤1 C (map ψG es) (map injL xs ++ map injR ys) →
  --   coeC (mixed-stack-G es xs ys) (pe-termC (map ψG es)
  --        (map injL xs ++ map injR ys))  ≈Term  GFactored es xs ys
  --
  -- The hypothesis supplies, via `Reservoir≤1⇒Unique`, the per-edge keystone
  -- `Unique` of the running stack at every cons; it is advanced one
  -- `edge-step` per recursion by `edge-step-Reservoir≤1`.

  -- `ψG` is `_↑ˡ K.nE`; `map ψG es ≡ map (_↑ˡ K.nE) es` definitionally.
  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  ------------------------------------------------------------------------
  -- ### Permute coherence helpers (the keystone, packaged for `pvlC`).

  -- Two `pvlC`-permutes with the SAME domain+codomain coincide, given the
  -- codomain is `Unique` — the keystone, at `C.vlab`.
  pvlC-coh
    : ∀ {zs ws : List (Fin C.nV)} → Unique ws → (p q : zs Perm.↭ ws)
    → pvlC p ≈Term pvlC q
  pvlC-coh uniq p q = permute-via-vlab-≈Term-coherence-K Kf C.vlab uniq p q

  -- `pvlC permC ≈ coeC (sym e) (pvlC q)` when `permC : zs ↭ ws` and the
  -- `head-factor`-shaped perm `q : zs ↭ ws'` reach the SAME (Unique) list up
  -- to a codomain LIST equality `e : ws ≡ ws'`.  `e`-`refl`-match collapses
  -- `coeC` to identity; then the keystone closes the common Unique codomain.
  pvlC-reconcile
    : ∀ {zs : List (Fin C.nV)} {ws ws' : List (Fin C.nV)}
        (e : ws ≡ ws') (permC : zs Perm.↭ ws) (q : zs Perm.↭ ws')
    → Unique ws'
    → pvlC permC ≈Term coeC {zs} (sym e) (pvlC q)
  pvlC-reconcile refl permC q uniq = pvlC-coh uniq permC q

  ------------------------------------------------------------------------
  -- ### head box reconciliation.
  --
  -- The single-FIRE-edge box `fire-mid C (ψG e) (injL restG ++ injR ys)`
  -- (framed in `process-edges`' `A++(B++C)` shape, residual un-split) IS
  -- `head-factor`'s `Box` (the `whole-eq`-substituted box-of on
  -- `g = C.elab (ψG e)`, residual split + `++-assoc`'d into the
  -- `(A++B)++C` shape), modulo a single `subst₂` framing transport that
  -- `objUIP` collapses (`box-rest-rewrite` is the residual split; the rest
  -- is two `subst₂-HomTerm-∘` recombinations + `objUIP`).
  Box-of-head
    : (e : Fin G.nE) (restG : List (Fin G.nV)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab ((C.ein  (ψG e) ++ map injL restG) ++ map injR ys)))
              (unflatten (map C.vlab ((C.eout (ψG e) ++ map injL restG) ++ map injR ys)))
  Box-of-head e restG ys =
    subst₂ HomTerm
      (cong unflatten (whole-eq (C.ein  (ψG e)) (map injL restG) ys))
      (cong unflatten (whole-eq (C.eout (ψG e)) (map injL restG) ys))
      (box-of (map C.vlab (C.ein (ψG e))) (map C.vlab (C.eout (ψG e)))
              (map C.vlab (map injL restG) ++ Rys-flat ys)
              (C.elab (ψG e)))

  -- `Box-of-head` is the `++-assoc`-transport of `fire-mid` on the un-split
  -- residual `injL restG ++ injR ys`.
  fire-mid-to-Box-≡
    : (e : Fin G.nE) (restG : List (Fin G.nV)) (ys : List (Fin K.nV))
    → (dEq : map C.vlab (C.ein  (ψG e) ++ (map injL restG ++ map injR ys))
           ≡ map C.vlab ((C.ein  (ψG e) ++ map injL restG) ++ map injR ys))
      (cEq : map C.vlab (C.eout (ψG e) ++ (map injL restG ++ map injR ys))
           ≡ map C.vlab ((C.eout (ψG e) ++ map injL restG) ++ map injR ys))
    → subst₂ HomTerm (cong unflatten dEq) (cong unflatten cEq)
        (fire-mid C-hg (ψG e) (map injL restG ++ map injR ys))
      ≡ Box-of-head e restG ys
  fire-mid-to-Box-≡ e restG ys dEq cEq = goal-≡
    where
      eiL = map C.vlab (C.ein  (ψG e))
      eoL = map C.vlab (C.eout (ψG e))
      restC = map injL restG ++ map injR ys
      g  = C.elab (ψG e)

      rsplit : map C.vlab restC ≡ map C.vlab (map injL restG) ++ Rys-flat ys
      rsplit = map-++ C.vlab (map injL restG) (map injR ys)

      box-base = box-of eiL eoL (map C.vlab restC) g

      -- the box-of on the split residual is the subst of box-base.
      bx-rest : box-of eiL eoL (map C.vlab (map injL restG) ++ Rys-flat ys) g
              ≡ subst₂ HomTerm
                  (cong unflatten (cong (eiL ++_) rsplit))
                  (cong unflatten (cong (eoL ++_) rsplit))
                  box-base
      bx-rest = sym (box-rest-rewrite eiL eoL rsplit g)

      goal-≡
        : subst₂ HomTerm (cong unflatten dEq) (cong unflatten cEq)
            (fire-mid C-hg (ψG e) restC)
          ≡ Box-of-head e restG ys
      goal-≡ =
        trans
          -- LHS: subst₂ dEq/cEq (subst₂ (fire-mid framing) box-base)
          (cong (subst₂ HomTerm (cong unflatten dEq) (cong unflatten cEq))
                (refl {x = fire-mid C-hg (ψG e) restC}))
        (trans
          (subst₂-HomTerm-∘
             (cong unflatten (sym (map-++ C.vlab (C.ein  (ψG e)) restC)))
             (cong unflatten dEq)
             (cong unflatten (sym (map-++ C.vlab (C.eout (ψG e)) restC)))
             (cong unflatten cEq)
             box-base)
        (trans
          -- collapse to the whole-eq framing over box-base via objUIP.
          (cong₂ (λ p q → subst₂ HomTerm p q box-base)
                 (objUIP _ (trans (cong unflatten (cong (eiL ++_) rsplit))
                                  (cong unflatten (whole-eq (C.ein  (ψG e)) (map injL restG) ys))))
                 (objUIP _ (trans (cong unflatten (cong (eoL ++_) rsplit))
                                  (cong unflatten (whole-eq (C.eout (ψG e)) (map injL restG) ys)))))
          -- split back: whole-eq ∘ box-rest, then fold box-rest into the inner box.
          (trans
            (sym (subst₂-HomTerm-∘
                    (cong unflatten (cong (eiL ++_) rsplit))
                    (cong unflatten (whole-eq (C.ein  (ψG e)) (map injL restG) ys))
                    (cong unflatten (cong (eoL ++_) rsplit))
                    (cong unflatten (whole-eq (C.eout (ψG e)) (map injL restG) ys))
                    box-base))
            (cong (subst₂ HomTerm
                     (cong unflatten (whole-eq (C.ein  (ψG e)) (map injL restG) ys))
                     (cong unflatten (whole-eq (C.eout (ψG e)) (map injL restG) ys)))
                  (sym bx-rest)))))

  -- `Unique` of a `++` restricts to the left prefix.
  Unique-++ˡ : ∀ {a} {A : Set a} (xs : List A) {ys : List A}
             → Unique (xs ++ ys) → Unique xs
  Unique-++ˡ []       _        = []
  Unique-++ˡ (x ∷ xs) (px ∷ u) = AllProp.++⁻ˡ xs px ∷ Unique-++ˡ xs u

  -- `coeC` (codomain transport) distributes over `∘` on the cod factor.
  coeC-∘
    : ∀ {d m : List (Fin C.nV)} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        (f : HomTerm (unflatten (map C.vlab m)) (unflatten (map C.vlab s)))
        (g : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab m)))
    → coeC {d} eq (f ∘ g) ≡ coeC {m} eq f ∘ g
  coeC-∘ refl f g = refl

  ------------------------------------------------------------------------
  -- ### `fire-core` — `fire-case` with the C-residuals already in their
  -- canonical lifted form (`map injL restG ++ map injR ys` / `map injL
  -- restG`).  `fire-case` reduces to this by `extract-prefix` determinism.
  --
  -- The mixed FIRE box slides past `uf++` via `head-factor` (with
  -- `eiBlk = C.ein (ψG e)`, `rgBlk = map injL restG`, `g = C.elab (ψG e)`,
  -- `p = permCl`); the two FIRE permutes + the `++-assoc`/eout-c box
  -- framings are reconciled by `fire-mid-to-Box-≡` and the keystone (the
  -- choice of `p` is immaterial — the keystone makes any two perms into the
  -- shared `Unique` codomain coincide).
  fire-core
    : (e : Fin G.nE) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → Unique (map injL xs ++ map injR ys)
    → (restG : List (Fin G.nV))
      (permCm : map injL xs ++ map injR ys
                Perm.↭ C.ein (ψG e) ++ (map injL restG ++ map injR ys))
      (permCl : map injL xs Perm.↭ C.ein (ψG e) ++ map injL restG)
    → (mEq : C.eout (ψG e) ++ (map injL restG ++ map injR ys)
           ≡ map injL (G.eout e ++ restG) ++ map injR ys)
    → (lEq : C.eout (ψG e) ++ map injL restG ≡ map injL (G.eout e ++ restG))
    → coeC {map injL xs ++ map injR ys} mEq
        (fire-term C-hg (ψG e) (map injL xs ++ map injR ys)
                   (map injL restG ++ map injR ys) permCm)
      ≈Term _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) (map injR ys))
            ∘ (coeC {map injL xs} lEq
                 (fire-term C-hg (ψG e) (map injL xs) (map injL restG) permCl)
               ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
  -- codomain-only transport (any ObjTerm domain), for the `⊗₀`-domained
  -- `uf++` composites.
  coCod : ∀ {D : ObjTerm} {s s' : List (Fin C.nV)} → s ≡ s'
        → HomTerm D (unflatten (map C.vlab s)) → HomTerm D (unflatten (map C.vlab s'))
  coCod {D} eq = subst (λ z → HomTerm D (unflatten (map C.vlab z))) eq

  coCod-resp-≈
    : ∀ {D : ObjTerm} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        {f h : HomTerm D (unflatten (map C.vlab s))}
    → f ≈Term h → coCod eq f ≈Term coCod eq h
  coCod-resp-≈ refl f≈h = f≈h

  -- domain-only transport.
  coDom : ∀ {D : ObjTerm} {s s' : List (Fin C.nV)} → s ≡ s'
        → HomTerm (unflatten (map C.vlab s)) D → HomTerm (unflatten (map C.vlab s')) D
  coDom {D} eq = subst (λ z → HomTerm (unflatten (map C.vlab z)) D) eq

  -- slide a codomain transport across a composite: `f ∘ coCod (sym eq) g`
  -- pushes `eq` onto `f`'s domain.
  ∘-coCod-slide
    : ∀ {D E : ObjTerm} {a b : List (Fin C.nV)} (eq : a ≡ b)
        (f : HomTerm (unflatten (map C.vlab b)) E)
        (g : HomTerm D (unflatten (map C.vlab a)))
    → f ∘ coCod eq g ≡ coDom (sym eq) f ∘ g
  ∘-coCod-slide refl f g = refl

  -- `coeC` and `coCod`/`coDom` interaction: `coeC eq f` viewed as `coCod`,
  -- and a `subst₂ HomTerm`-on-both-ends as `coCod ∘ coDom`.
  subst₂-as-coCod-coDom
    : ∀ {a b c d : List (Fin C.nV)} (p : a ≡ b) (q : c ≡ d)
        (f : HomTerm (unflatten (map C.vlab a)) (unflatten (map C.vlab c)))
    → subst₂ HomTerm (cong unflatten (cong (map C.vlab) p))
                     (cong unflatten (cong (map C.vlab) q)) f
      ≡ coCod q (coDom p f)
  subst₂-as-coCod-coDom refl refl f = refl

  -- `coCod` of a `trans` factors; `coDom`/`coCod` commute.
  coCod-trans
    : ∀ {D : ObjTerm} {a b c : List (Fin C.nV)} (p : a ≡ b) (q : b ≡ c)
        (f : HomTerm D (unflatten (map C.vlab a)))
    → coCod (trans p q) f ≡ coCod q (coCod p f)
  coCod-trans refl refl f = refl

  coDom-coCod-comm
    : ∀ {a b c d : List (Fin C.nV)} (p : a ≡ b) (q : c ≡ d)
        (f : HomTerm (unflatten (map C.vlab a)) (unflatten (map C.vlab c)))
    → coDom p (coCod q f) ≡ coCod q (coDom p f)
  coDom-coCod-comm refl refl f = refl

  -- `coCod` commutes with precomposition.
  coCod-∘ʳ
    : ∀ {D E : ObjTerm} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        (f : HomTerm E (unflatten (map C.vlab s))) (h : HomTerm D E)
    → coCod eq f ∘ h ≡ coCod eq (f ∘ h)
  coCod-∘ʳ refl f h = refl

  -- `coeC eq f = coCod eq f` for a `U(map C.vlab d)`-domained term (the two
  -- transports agree; `coeC` is `coCod` specialised to that domain).
  coeC≡coCod
    : ∀ {d : List (Fin C.nV)} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        (f : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s)))
    → coeC {d} eq f ≡ coCod eq f
  coeC≡coCod refl f = refl

  -- `to(uf++ A' Rys) ∘ (coeC lEq X ⊗₁ id)` slides the block-1 transport
  -- onto the composite's codomain (eq-refl-match).
  to-uf++-blk1
    : ∀ {A A' : List (Fin C.nV)} (eq : A ≡ A') (Rs : List (Fin C.nV))
        {d : List (Fin C.nV)}
        (X : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab A)))
    → _≅_.to (BTC.uf++ A' Rs) ∘ (coeC {d} eq X ⊗₁ id {unflatten (map C.vlab Rs)})
      ≈Term coCod (cong (_++ Rs) eq)
              (_≅_.to (BTC.uf++ A Rs) ∘ (X ⊗₁ id {unflatten (map C.vlab Rs)}))
  to-uf++-blk1 refl Rs X = ≈-Term-refl

  fire-core e xs ys uniq restG permCm permCl mEq lEq = goal
    where
      s = map injL xs ++ map injR ys
      eiB = C.ein  (ψG e)
      eoB = C.eout (ψG e)
      rgB = map injL restG
      g  = C.elab (ψG e)
      Rys = map injR ys

      open FM.HomReasoning

      -- the `head-factor` perm: `permCl` itself works (the keystone makes
      -- the exact choice immaterial — only the Unique codomain matters).
      pL : map injL xs Perm.↭ eiB ++ rgB
      pL = permCl

      -- the FIRE box on the un-split residual (LHS form).
      fmM = fire-mid C-hg (ψG e) (rgB ++ Rys)
      fmL = fire-mid C-hg (ψG e) rgB

      -- the head-factor RHS pure-L box `BoxSub` IS `fmL` definitionally.
      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiB rgB)))
                 (cong unflatten (sym (map-++ C.vlab eoB rgB)))
                 (box-of (map C.vlab eiB) (map C.vlab eoB) (map C.vlab rgB) g)

      BoxSub≡fmL : BoxSub ≡ fmL
      BoxSub≡fmL = refl

      -- Unique of the lifted codomain (for the keystone), via `Unique-resp-↭`.
      uniqMix : Unique (eiB ++ (rgB ++ Rys))
      uniqMix = SU.Unique-resp-↭ permCm uniq
      uniqL : Unique (eiB ++ rgB)
      uniqL = SU.Unique-resp-↭ permCl (Unique-++ˡ (map injL xs) uniq)
      uniqMix' : Unique ((eiB ++ rgB) ++ Rys)
      uniqMix' = SU.Unique-resp-↭ (PermProp.++⁺ pL (Perm.↭-refl {x = Rys})) uniq

      e₀ : eiB ++ (rgB ++ Rys) ≡ (eiB ++ rgB) ++ Rys
      e₀ = sym (++-assoc eiB rgB Rys)

      Box = Box-of-head e restG ys
      ppL = PermProp.++⁺ pL (Perm.↭-refl {x = Rys})

      -- the common middle: `coCod (cong (_++Rys) lEq) (Box ∘ pvlC ppL)`.
      Mid = coCod {unflatten (map C.vlab s)} (cong (_++ Rys) lEq) (Box ∘ pvlC ppL)

      -- RHS reconciliation: head-factor RHS, block-1 transport + perm keystone.
      hf : Box ∘ pvlC ppL
         ≈Term _≅_.to (BTC.uf++ (eoB ++ rgB) Rys)
               ∘ ((fmL ∘ pvlC pL) ⊗₁ id {unflatten (map C.vlab Rys)})
               ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
      hf = head-factor eiB eoB rgB xs ys g pL

      rhs≈Mid
        : _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) Rys)
          ∘ (coeC {map injL xs} lEq (fmL ∘ pvlC permCl) ⊗₁ id {RsufObj ys})
          ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
          ≈Term Mid
      rhs≈Mid = begin
        _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) Rys)
          ∘ (coeC {map injL xs} lEq (fmL ∘ pvlC pL) ⊗₁ id {unflatten (map C.vlab Rys)})
          ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
          ≈⟨ FM.sym-assoc ⟩
        (_≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) Rys)
          ∘ (coeC {map injL xs} lEq (fmL ∘ pvlC pL) ⊗₁ id {unflatten (map C.vlab Rys)}))
          ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
          ≈⟨ ∘-resp-≈ (to-uf++-blk1 lEq Rys (fmL ∘ pvlC pL)) ≈-Term-refl ⟩
        coCod (cong (_++ Rys) lEq)
          (_≅_.to (BTC.uf++ (eoB ++ rgB) Rys)
           ∘ ((fmL ∘ pvlC pL) ⊗₁ id {unflatten (map C.vlab Rys)}))
          ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
          ≈⟨ ≡⇒≈Term (coCod-∘ʳ (cong (_++ Rys) lEq) _ _) ⟩
        coCod (cong (_++ Rys) lEq)
          ((_≅_.to (BTC.uf++ (eoB ++ rgB) Rys)
            ∘ ((fmL ∘ pvlC pL) ⊗₁ id {unflatten (map C.vlab Rys)}))
           ∘ _≅_.from (BTC.uf++ (map injL xs) Rys))
          ≈⟨ coCod-resp-≈ (cong (_++ Rys) lEq)
                (≈-Term-trans FM.assoc (≈-Term-sym hf)) ⟩
        Mid ∎

      -- the box-of cod equation as a `trans` through head-factor's `(A++B)++C`.
      cEq-assoc : eoB ++ (rgB ++ Rys) ≡ (eoB ++ rgB) ++ Rys
      cEq-assoc = sym (++-assoc eoB rgB Rys)
      mEq-split : mEq ≡ trans cEq-assoc (cong (_++ Rys) lEq)
      mEq-split = uipL mEq (trans cEq-assoc (cong (_++ Rys) lEq))

      -- `coDom e₀ (coCod cEq-assoc fmM) ≡ Box` (fire-mid-to-Box, recast).
      Box≡ : coCod cEq-assoc (coDom e₀ fmM) ≡ Box
      Box≡ =
        trans (sym (subst₂-as-coCod-coDom e₀ cEq-assoc fmM))
              (≈Term⇒≡-box)
        where
          -- fire-mid-to-Box gives the ≈Term; its proof is `≡⇒≈Term`, so the
          -- underlying ≡ holds — re-derive it by the same subst chain.
          ≈Term⇒≡-box
            : subst₂ HomTerm (cong unflatten (cong (map C.vlab) e₀))
                             (cong unflatten (cong (map C.vlab) cEq-assoc)) fmM
              ≡ Box
          ≈Term⇒≡-box = fire-mid-to-Box-≡ e restG ys
                          (cong (map C.vlab) e₀)
                          (cong (map C.vlab) cEq-assoc)

      lhs≈Mid
        : coeC {s} mEq (fire-term C-hg (ψG e) s (rgB ++ Rys) permCm)
          ≈Term Mid
      lhs≈Mid = begin
        coeC {s} mEq (fmM ∘ pvlC permCm)
          ≈⟨ ≡⇒≈Term (coeC-∘ mEq fmM (pvlC permCm)) ⟩
        coeC {eiB ++ (rgB ++ Rys)} mEq fmM ∘ pvlC permCm
          ≈⟨ ∘-resp-≈ ≈-Term-refl
               (pvlC-reconcile e₀ permCm ppL uniqMix') ⟩
        coeC {eiB ++ (rgB ++ Rys)} mEq fmM ∘ coeC {s} (sym e₀) (pvlC ppL)
          ≈⟨ ≡⇒≈Term (cong₂ _∘_ (coeC≡coCod mEq fmM)
                                 (coeC≡coCod (sym e₀) (pvlC ppL))) ⟩
        coCod mEq fmM ∘ coCod (sym e₀) (pvlC ppL)
          ≈⟨ ≡⇒≈Term (∘-coCod-slide (sym e₀) (coCod mEq fmM) (pvlC ppL)) ⟩
        coDom (sym (sym e₀)) (coCod mEq fmM) ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (cong (λ z → coDom z (coCod mEq fmM) ∘ pvlC ppL)
                           (sym²e₀)) ⟩
        coDom e₀ (coCod mEq fmM) ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (cong (λ z → coDom e₀ (coCod z fmM) ∘ pvlC ppL) mEq-split) ⟩
        coDom e₀ (coCod (trans cEq-assoc (cong (_++ Rys) lEq)) fmM) ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (cong (λ z → coDom e₀ z ∘ pvlC ppL)
                           (coCod-trans cEq-assoc (cong (_++ Rys) lEq) fmM)) ⟩
        coDom e₀ (coCod (cong (_++ Rys) lEq) (coCod cEq-assoc fmM)) ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (cong (_∘ pvlC ppL)
                           (coDom-coCod-comm e₀ (cong (_++ Rys) lEq)
                              (coCod cEq-assoc fmM))) ⟩
        coCod (cong (_++ Rys) lEq) (coDom e₀ (coCod cEq-assoc fmM)) ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (cong (λ z → coCod (cong (_++ Rys) lEq) z ∘ pvlC ppL)
                           (trans (coDom-coCod-comm e₀ cEq-assoc fmM) Box≡)) ⟩
        coCod (cong (_++ Rys) lEq) Box ∘ pvlC ppL
          ≈⟨ ≡⇒≈Term (coCod-∘ʳ (cong (_++ Rys) lEq) Box (pvlC ppL)) ⟩
        Mid ∎
        where
          sym²e₀ : sym (sym e₀) ≡ e₀
          sym²e₀ = BoxAssoc.sym² e₀

      goal
        : coeC {s} mEq (fire-term C-hg (ψG e) s (rgB ++ Rys) permCm)
          ≈Term _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) Rys)
                ∘ (coeC {map injL xs} lEq (fmL ∘ pvlC permCl) ⊗₁ id {RsufObj ys})
                ∘ _≅_.from (BTC.uf++ (map injL xs) Rys)
      goal = ≈-Term-trans lhs≈Mid (≈-Term-sym rhs≈Mid)

  ------------------------------------------------------------------------
  -- ### `fire-case` — the FIRE/FIRE/FIRE core of `edge-suffix-factor`.
  fire-case
    : (e : Fin G.nE) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → Unique (map injL xs ++ map injR ys)
    → (restG : List (Fin G.nV)) (pG : xs Perm.↭ G.ein e ++ restG)
      (eqG : extract-prefix (G.ein e) xs ≡ just (restG , pG))
    → (restCm : List (Fin C.nV))
      (permCm : map injL xs ++ map injR ys Perm.↭ C.ein (ψG e) ++ restCm)
      (eqCm : extract-prefix (C.ein (ψG e)) (map injL xs ++ map injR ys)
              ≡ just (restCm , permCm))
    → (restCl : List (Fin C.nV))
      (permCl : map injL xs Perm.↭ C.ein (ψG e) ++ restCl)
      (eqCl : extract-prefix (C.ein (ψG e)) (map injL xs) ≡ just (restCl , permCl))
    → (mEq : C.eout (ψG e) ++ restCm ≡ map injL (G.eout e ++ restG) ++ map injR ys)
    → (lEq : C.eout (ψG e) ++ restCl ≡ map injL (G.eout e ++ restG))
    → coeC {map injL xs ++ map injR ys} mEq
        (fire-term C-hg (ψG e) (map injL xs ++ map injR ys) restCm permCm)
      ≈Term _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) (map injR ys))
            ∘ (coeC {map injL xs} lEq
                 (fire-term C-hg (ψG e) (map injL xs) restCl permCl)
               ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
  fire-case e xs ys uniq restG pG eqG restCm permCm eqCm restCl permCl eqCl mEq lEq =
    collapse restCm permCm mEq restCl permCl lEq restCm≡ restCl≡
    where
      s = map injL xs ++ map injR ys

      -- determinism: the C-mixed residual IS the lifted G-residual.
      mixed-lift
        : ∃[ q ] extract-prefix (C.ein (ψG e)) s
                 ≡ just (map injL restG ++ map injR ys , q)
      mixed-lift =
        subst (λ ks → ∃[ q ] extract-prefix ks s
                              ≡ just (map injL restG ++ map injR ys , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-↑ˡ-on-mixed-just K.nV (G.ein e) xs ys restG pG eqG)

      restCm≡ : restCm ≡ map injL restG ++ map injR ys
      restCm≡ = cong proj₁ (just-injective (trans (sym eqCm) (proj₂ mixed-lift)))

      pureL-lift
        : ∃[ q ] extract-prefix (C.ein (ψG e)) (map injL xs)
                 ≡ just (map injL restG , q)
      pureL-lift =
        subst (λ ks → ∃[ q ] extract-prefix ks (map injL xs)
                              ≡ just (map injL restG , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-just injL
                 (λ {x} {y} → ↑ˡ-injective K.nV x y) (G.ein e) xs restG pG eqG)

      restCl≡ : restCl ≡ map injL restG
      restCl≡ = cong proj₁ (just-injective (trans (sym eqCl) (proj₂ pureL-lift)))

      -- collapse BOTH residuals into canonical form (matched at refl/refl),
      -- reducing the goal to `fire-core`.
      collapse
        : ∀ (rCm : List (Fin C.nV)) (pCm : s Perm.↭ C.ein (ψG e) ++ rCm)
            (mEq₀ : C.eout (ψG e) ++ rCm ≡ map injL (G.eout e ++ restG) ++ map injR ys)
            (rCl : List (Fin C.nV)) (pCl : map injL xs Perm.↭ C.ein (ψG e) ++ rCl)
            (lEq₀ : C.eout (ψG e) ++ rCl ≡ map injL (G.eout e ++ restG))
            (rCm≡ : rCm ≡ map injL restG ++ map injR ys)
            (rCl≡ : rCl ≡ map injL restG)
        → coeC {s} mEq₀ (fire-term C-hg (ψG e) s rCm pCm)
          ≈Term _≅_.to (BTC.uf++ (map injL (G.eout e ++ restG)) (map injR ys))
                ∘ (coeC {map injL xs} lEq₀
                     (fire-term C-hg (ψG e) (map injL xs) rCl pCl)
                   ⊗₁ id {RsufObj ys})
                ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
      collapse rCm pCm mEq₀ rCl pCl lEq₀ refl refl =
        fire-core e xs ys uniq restG pCm pCl mEq₀ lEq₀

  ------------------------------------------------------------------------
  -- ### `edge-suffix-factor` — the per-edge mixed-vs-pure-L factorization.
  --
  -- Over the THREE `EdgeStepR` relation witnesses (G-side, mixed-C,
  -- pure-L-C), with the two stack-agreement equalities `mEq`/`lEq`:
  --
  --   coeC mEq tCm
  --     ≈Term to(uf++ (map injL xs') Rys) ∘ (coeC lEq tCl ⊗₁ id) ∘ from(uf++ … Rys)
  --
  -- The G-side witness `wG` drives the firing dispatch; the lifting lemmas
  -- rule out the cross (G-fires/C-skips, G-skips/C-fires) cases.
  --
  -- SKIP: both C terms are `id`, `xs' = xs`, closed by `id-as-tensor` + a
  -- framing collapse (`subst₂-id` via `uipL`).
  -- FIRE: `head-factor` slides the mixed FIRE box past `uf++` as `(pure-L
  -- FIRE box ⊗₁ id)`; the two FIRE permutes + the `++-assoc` box framings are
  -- reconciled via the keystone (`pvlC-reconcile`/`pvlC-coh`, `Unique`-fed) and
  -- `fire-mid-to-Box`.
  edge-suffix-factor
    : (e : Fin G.nE) (xs xs' : List (Fin G.nV)) (ys : List (Fin K.nV))
    → Unique (map injL xs ++ map injR ys)
    → ∀ {tG : HomTerm (unflatten (map G.vlab xs)) (unflatten (map G.vlab xs'))}
        {s'Cm : List (Fin C.nV)}
        {tCm : HomTerm (unflatten (map C.vlab (map injL xs ++ map injR ys)))
                       (unflatten (map C.vlab s'Cm))}
        {s'Cl : List (Fin C.nV)}
        {tCl : HomTerm (unflatten (map C.vlab (map injL xs)))
                       (unflatten (map C.vlab s'Cl))}
    → EdgeStepR G xs e xs' tG
    → EdgeStepR C-hg (map injL xs ++ map injR ys) (ψG e) s'Cm tCm
    → EdgeStepR C-hg (map injL xs) (ψG e) s'Cl tCl
    → (mEq : s'Cm ≡ map injL xs' ++ map injR ys)
    → (lEq : s'Cl ≡ map injL xs')
    → coeC {map injL xs ++ map injR ys} mEq tCm
      ≈Term _≅_.to (BTC.uf++ (map injL xs') (map injR ys))
            ∘ (coeC {map injL xs} lEq tCl ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
  -- SKIP/SKIP/SKIP.  Both C terms are `id`, xs' = xs; `coeC ·-refl id = id`.
  edge-suffix-factor e xs .xs ys uniq (skipR eqG) (skipR eqCm) (skipR eqCl) mEq lEq =
    ≈-Term-trans
      (≡⇒≈Term (cong (λ z → coeC {map injL xs ++ map injR ys} z id)
                     (uipL mEq refl)))
      (≈-Term-trans (id-as-tensor (map injL xs) (map injR ys))
        (∘-resp-≈ ≈-Term-refl
          (∘-resp-≈
            (⊗-resp-≈
              (≡⇒≈Term (sym (cong (λ z → coeC {map injL xs} z id) (uipL lEq refl))))
              ≈-Term-refl)
            ≈-Term-refl)))
  -- G skips but mixed-C fires: impossible (mixed-nothing lifting).
  edge-suffix-factor e xs xs' ys uniq (skipR eqG) (fireR restCm permCm eqCm) _ mEq lEq =
    ⊥-elim (just≢nothing (trans (sym eqCm) cNothing))
    where
      cNothing : extract-prefix (C.ein (ψG e)) (map injL xs ++ map injR ys) ≡ nothing
      cNothing =
        subst (λ ks → extract-prefix ks (map injL xs ++ map injR ys) ≡ nothing)
              (sym (ein-c-inj₁-red e))
              (extract-prefix-↑ˡ-on-mixed-nothing K.nV (G.ein e) xs ys eqG)
  -- G skips but pure-L-C fires: impossible.
  edge-suffix-factor e xs xs' ys uniq (skipR eqG) _ (fireR restCl permCl eqCl) mEq lEq =
    ⊥-elim (just≢nothing (trans (sym eqCl) clNothing))
    where
      clNothing : extract-prefix (C.ein (ψG e)) (map injL xs) ≡ nothing
      clNothing =
        subst (λ ks → extract-prefix ks (map injL xs) ≡ nothing)
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-nothing injL
                 (λ {x} {y} → ↑ˡ-injective K.nV x y) (G.ein e) xs eqG)
  -- G fires but mixed-C skips: impossible.
  edge-suffix-factor e xs xs' ys uniq (fireR restG pG eqG) (skipR eqCm) _ mEq lEq =
    ⊥-elim (just≢nothing (trans (sym (proj₂ transp)) eqCm))
    where
      transp =
        subst (λ ks → ∃[ q ] extract-prefix ks (map injL xs ++ map injR ys)
                              ≡ just (map injL restG ++ map injR ys , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-↑ˡ-on-mixed-just K.nV (G.ein e) xs ys restG pG eqG)
  -- G fires but pure-L-C skips: impossible.
  edge-suffix-factor e xs xs' ys uniq (fireR restG pG eqG) _ (skipR eqCl) mEq lEq =
    ⊥-elim (just≢nothing (trans (sym (proj₂ transp)) eqCl))
    where
      transp =
        subst (λ ks → ∃[ q ] extract-prefix ks (map injL xs)
                              ≡ just (map injL restG , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-just injL
                 (λ {x} {y} → ↑ˡ-injective K.nV x y) (G.ein e) xs restG pG eqG)
  -- FIRE/FIRE/FIRE: the substantive case.
  edge-suffix-factor e xs .(G.eout e ++ restG) ys uniq
      (fireR restG pG eqG) (fireR restCm permCm eqCm) (fireR restCl permCl eqCl) mEq lEq =
    fire-case e xs ys uniq restG pG eqG restCm permCm eqCm restCl permCl eqCl mEq lEq

  ------------------------------------------------------------------------
  -- ### `gblock-factor` itself.
  --
  -- The G-edge block run from the MIXED dom `map injL xs ++ map injR ys`
  -- factors, modulo `BTC.uf++`, as the pure-injL block run (`Lterm`)
  -- tensored with `id` on the untouched `map injR ys` suffix.  Proven by
  -- induction on the edge list, threading the `Reservoir≤1` freshness
  -- invariant exactly like `StackEquivariance.process-edges-equivariant`:
  -- the head edge-step is factored by `edge-suffix-factor` (over the three
  -- `EdgeStepR` relation witnesses), and the tail by the IH; the two
  -- `(· ⊗₁ id)` blocks merge through the middle `from ∘ to = id` `uf++`
  -- cancellation + `⊗-∘-dist`.
  gblock-factor
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → SUR.Reservoir≤1 (hTensor G K) (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys)
    → coeC {map injL xs ++ map injR ys} (mixed-stack-G es xs ys)
        (pe-termC (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys))
      ≈Term GFactored es xs ys
  gblock-factor [] xs ys res =
    ≈-Term-trans
      (≡⇒≈Term (cong (λ z → coeC {map injL xs ++ map injR ys} z id)
                     (uipL (mixed-stack-G [] xs ys) refl)))
      (id-as-tensor (map injL xs) (map injR ys))
  gblock-factor (e ∷ es) xs ys res = goal
    where
      s = map injL xs ++ map injR ys
      Lxs = map injL xs
      Rys = map injR ys
      xs' = proj₁ (edge-step G xs e)
      s1  = proj₁ (edge-step C-hg s (ψG e))
      tH  = proj₂ (edge-step C-hg s (ψG e))
      s1L = proj₁ (edge-step C-hg Lxs (ψG e))
      tHL = proj₂ (edge-step C-hg Lxs (ψG e))

      uniq-s : Unique s
      uniq-s = SUR.Reservoir≤1⇒Unique C-hg (map (_↑ˡ K.nE) (e ∷ es)) s res

      mEq : s1 ≡ map injL xs' ++ Rys
      mEq = cong proj₁ (proj₂ (edge-step-↑ˡ-on-mixed G K e xs ys))

      lEq : s1L ≡ map injL xs'
      lEq = TG.edge-step-stack-emb e xs

      -- reservoir advanced one edge for the tail.
      res-tail : SUR.Reservoir≤1 C-hg (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys)
      res-tail = subst (SUR.Reservoir≤1 C-hg (map (_↑ˡ K.nE) es)) mEq
                       (SUR.edge-step-Reservoir≤1 C-hg (ψG e) (map (_↑ˡ K.nE) es) s res)

      -- head edge-step factorization (over the three relation witnesses).
      head-fac
        : coeC {s} mEq tH
          ≈Term _≅_.to (BTC.uf++ (map injL xs') Rys)
                ∘ (coeC {Lxs} lEq tHL ⊗₁ id {RsufObj ys})
                ∘ _≅_.from (BTC.uf++ Lxs Rys)
      head-fac = edge-suffix-factor e xs xs' ys uniq-s
                   (edge-step-graph G xs e)
                   (edge-step-graph C-hg s (ψG e))
                   (edge-step-graph C-hg Lxs (ψG e))
                   mEq lEq

      open FM.HomReasoning

      IH : coeC {map injL xs' ++ Rys} (mixed-stack-G es xs' ys)
             (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys))
           ≈Term GFactored es xs' ys
      IH = gblock-factor es xs' ys res-tail

      -- pure-L composition: the pure-injL run's head ∘ tail IS `Lterm (e∷es)`.
      -- Generalise the pure-L head stack `s1Lᵍ`/term `tHLᵍ`/stack-emb `wEqL`
      -- so `lEqᵍ` can be matched at refl (the real `s1L` is a stuck
      -- `edge-step` projection), then `coeC-∘` + `uipL` on `proc-stack-emb-L`.
      Lterm-cons
        : ∀ (s1Lᵍ : List (Fin C.nV))
            (tHLᵍ : HomTerm (unflatten (map C.vlab Lxs)) (unflatten (map C.vlab s1Lᵍ)))
            (lEqᵍ : s1Lᵍ ≡ map injL xs')
            (wEqL : pe-stackC (map (_↑ˡ K.nE) es) s1Lᵍ
                    ≡ map injL (pe-stackG (e ∷ es) xs))
        → Lterm es xs' ∘ coeC {Lxs} lEqᵍ tHLᵍ
          ≈Term coeC {Lxs} wEqL (pe-termC (map (_↑ˡ K.nE) es) s1Lᵍ ∘ tHLᵍ)
      Lterm-cons .(map injL xs') tHLᵍ refl wEqL =
        ≡⇒≈Term
          (trans (sym (coeC-∘ (proc-stack-emb-L es xs')
                    (pe-termC (map (_↑ˡ K.nE) es) (map injL xs')) tHLᵍ))
          (cong (λ z → coeC {Lxs} z
                   (pe-termC (map (_↑ˡ K.nE) es) (map injL xs') ∘ tHLᵍ))
                (uipL (proc-stack-emb-L es xs') wEqL)))

      -- combine: match the MIXED stack agreement at refl (over generalised
      -- `s1ᵍ`/`tHᵍ`, so the stuck `edge-step` projection does not block
      -- unification), then cancel the middle `from ∘ to = id` and merge the
      -- `(· ⊗₁ id)` via `⊗-∘-dist`.  The pure-L head `Lhead` and its
      -- composition fact `Lterm-fact` are passed in (proven concretely, via
      -- `Lterm-cons`, where the real `lEq`/`tHL` are in scope).
      combine
        : ∀ (s1ᵍ : List (Fin C.nV))
            (tHᵍ : HomTerm (unflatten (map C.vlab s)) (unflatten (map C.vlab s1ᵍ)))
            (Lhead : HomTerm (unflatten (map C.vlab Lxs))
                             (unflatten (map C.vlab (map injL xs'))))
        → (mEq₀ : s1ᵍ ≡ map injL xs' ++ Rys)
        → (wholeEq : pe-stackC (map (_↑ˡ K.nE) es) s1ᵍ
                     ≡ map injL (pe-stackG (e ∷ es) xs) ++ Rys)
        → coeC {s} mEq₀ tHᵍ
          ≈Term _≅_.to (BTC.uf++ (map injL xs') Rys)
                ∘ (Lhead ⊗₁ id {RsufObj ys})
                ∘ _≅_.from (BTC.uf++ Lxs Rys)
        → Lterm es xs' ∘ Lhead ≈Term Lterm (e ∷ es) xs
        → coeC {s} wholeEq
            (pe-termC (map (_↑ˡ K.nE) es) s1ᵍ ∘ tHᵍ)
          ≈Term GFactored (e ∷ es) xs ys
      combine .(map injL xs' ++ Rys) tHᵍ Lhead refl wholeEq head Lterm-fact = begin
        coeC {s} wholeEq
          (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys) ∘ tHᵍ)
          ≈⟨ ≡⇒≈Term (coeC-∘ wholeEq
                            (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys)) tHᵍ) ⟩
        coeC {map injL xs' ++ Rys} wholeEq
          (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys)) ∘ tHᵍ
          ≈⟨ ∘-resp-≈ (≡⇒≈Term (cong (λ z → coeC {map injL xs' ++ Rys} z
                                          (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys)))
                                      (uipL wholeEq
                                            (mixed-stack-G es xs' ys))))
                      ≈-Term-refl ⟩
        coeC {map injL xs' ++ Rys} (mixed-stack-G es xs' ys)
          (pe-termC (map (_↑ˡ K.nE) es) (map injL xs' ++ Rys)) ∘ tHᵍ
          ≈⟨ ∘-resp-≈ IH head ⟩
        GFactored es xs' ys
          ∘ (_≅_.to (BTC.uf++ (map injL xs') Rys)
             ∘ (Lhead ⊗₁ id {RsufObj ys})
             ∘ _≅_.from (BTC.uf++ Lxs Rys))
          ≈⟨ cancel-merge ⟩
        _≅_.to (BTC.uf++ (map injL (pe-stackG es xs')) Rys)
          ∘ ((Lterm es xs' ∘ Lhead) ⊗₁ id {RsufObj ys})
          ∘ _≅_.from (BTC.uf++ Lxs Rys)
          ≈⟨ ∘-resp-≈ ≈-Term-refl
               (∘-resp-≈ (⊗-resp-≈ Lterm-fact ≈-Term-refl) ≈-Term-refl) ⟩
        _≅_.to (BTC.uf++ (map injL (pe-stackG es xs')) Rys)
          ∘ (Lterm (e ∷ es) xs ⊗₁ id {RsufObj ys})
          ∘ _≅_.from (BTC.uf++ Lxs Rys) ∎
        where
          Lxs'' = map injL (pe-stackG es xs')
          cancel-merge
            : GFactored es xs' ys
              ∘ (_≅_.to (BTC.uf++ (map injL xs') Rys)
                 ∘ (Lhead ⊗₁ id {RsufObj ys})
                 ∘ _≅_.from (BTC.uf++ Lxs Rys))
              ≈Term _≅_.to (BTC.uf++ Lxs'' Rys)
                    ∘ ((Lterm es xs' ∘ Lhead) ⊗₁ id {RsufObj ys})
                    ∘ _≅_.from (BTC.uf++ Lxs Rys)
          cancel-merge = begin
            (_≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ (Lterm es xs' ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ (map injL xs') Rys))
              ∘ (_≅_.to (BTC.uf++ (map injL xs') Rys)
                 ∘ (Lhead ⊗₁ id {RsufObj ys})
                 ∘ _≅_.from (BTC.uf++ Lxs Rys))
              ≈⟨ cancel-mid-iso (_≅_.to (BTC.uf++ Lxs'' Rys))
                   (Lterm es xs' ⊗₁ id {RsufObj ys})
                   (_≅_.from (BTC.uf++ (map injL xs') Rys))
                   (_≅_.to (BTC.uf++ (map injL xs') Rys))
                   (Lhead ⊗₁ id {RsufObj ys})
                   (_≅_.from (BTC.uf++ Lxs Rys))
                   (_≅_.isoʳ (BTC.uf++ (map injL xs') Rys)) ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ (Lterm es xs' ⊗₁ id {RsufObj ys})
              ∘ (Lhead ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ ((Lterm es xs' ⊗₁ id {RsufObj ys}) ∘ (Lhead ⊗₁ id {RsufObj ys}))
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ ((Lterm es xs' ∘ Lhead) ⊗₁ (id {RsufObj ys} ∘ id {RsufObj ys}))
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩∘⟨refl ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ ((Lterm es xs' ∘ Lhead) ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ Lxs Rys) ∎

      goal
        : coeC {s} (mixed-stack-G (e ∷ es) xs ys)
            (pe-termC (map (_↑ˡ K.nE) es) s1 ∘ tH)
          ≈Term GFactored (e ∷ es) xs ys
      goal = combine s1 tH (coeC {Lxs} lEq tHL) mEq
                     (mixed-stack-G (e ∷ es) xs ys) head-fac
                     (Lterm-cons s1L tHL lEq (proc-stack-emb-L (e ∷ es) xs))

  ------------------------------------------------------------------------
  -- ### Milestone 2b — the K-side PREFIX-CARRY factorization (`kblock-factor`).
  --
  -- The mirror of `gblock-factor` with LEFT/RIGHT swapped: the carried block
  -- is the `map injL P` PREFIX (held by `id` on the LEFT), and the K-edges
  -- `ψK e = G.nE ↑ʳ e` act on the `map injR` part.
  --
  -- THE EXTRA WRINKLE: a K-edge PREPENDS its `eout` (`map injR (K.eout e)`)
  -- to the FRONT of the running stack (before the carried `map injL P`
  -- prefix), so the actual post-edge mixed stack only `↭`s — not `≡`s — the
  -- clean `map injL P ++ map injR <K-stack'>` target.  We therefore CANNOT
  -- thread a clean stack `≡` (as the G-side does via `mixed-stack-G`).
  -- Instead the K-block factorization lands on the ACTUAL mixed-run codomain
  -- and carries an OUTER `pvlC` braid (`KBraid`) from that codomain to the
  -- clean `(id {prefix} ⊗₁ Kterm)` target; the braid is a `permute-via-vlab`
  -- coincidence on the `Unique` codomain, discharged by the keystone
  -- `permute-via-vlab-≈Term-coherence-K` exactly as in `fire-core`'s
  -- `pvlC-reconcile`.

  -- `ψK` is `G.nE ↑ʳ_`; `map ψK es ≡ map (G.nE ↑ʳ_) es` definitionally.
  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  pe-stackK : List (Fin K.nE) → List (Fin K.nV) → List (Fin K.nV)
  pe-stackK o s = proj₁ (process-edges K o s)

  -- Pure-R stack agreement (from the gate's `proc-stack-emb`, φ = injR).
  proc-stack-emb-R
    : (es : List (Fin K.nE)) (ys : List (Fin K.nV))
    → pe-stackC (map (G.nE ↑ʳ_) es) (map injR ys)
      ≡ map injR (pe-stackK es ys)
  proc-stack-emb-R es ys = TK.proc-stack-emb es ys

  -- The pure-R inner term, with its codomain transported from
  -- `pe-stackC (map ψK es) (map injR ys)` to `map injR (pe-stackK es ys)`.
  Kterm
    : (es : List (Fin K.nE)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injR ys)))
              (unflatten (map C.vlab (map injR (pe-stackK es ys))))
  Kterm es ys =
    coeC {map injR ys} (proc-stack-emb-R es ys)
         (pe-termC (map (G.nE ↑ʳ_) es) (map injR ys))

  -- The CLEAN K-side target: `(id {prefix} ⊗₁ Kterm)`, framed by `BTC.uf++`.
  -- (Mirror of `GFactored`, prefix on the LEFT.)
  KClean
    : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injL P ++ map injR ys)))
              (unflatten (map C.vlab (map injL P ++ map injR (pe-stackK es ys))))
  KClean es P ys =
    _≅_.to (BTC.uf++ (map injL P) (map injR (pe-stackK es ys)))
    ∘ (id {RpreObj P} ⊗₁ Kterm es ys)
    ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))

  -- The K-prepend braid: the ACTUAL mixed K-run output `↭`s the clean target
  -- `map injL P ++ map injR (pe-stackK es ys)` (the K-edge eouts prepend to the
  -- stack front).  Read off `process-edges-↑ʳ-on-perm` at the identity input
  -- perm.  (`injL = _↑ˡ K.nV`, `injR = G.nV ↑ʳ_` definitionally.)
  private
    KBraid-data
      : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      → ∃[ s' ] ∃[ t ]
           process-edges C-hg (map (G.nE ↑ʳ_) es) (map injL P ++ map injR ys)
             ≡ (s' , t)
         × s' Perm.↭ map injL P ++ map injR (pe-stackK es ys)
    KBraid-data es P ys =
      process-edges-↑ʳ-on-perm G K es (map injL P ++ map injR ys) P ys Perm.↭-refl

  KBraid
    : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → pe-stackC (map (G.nE ↑ʳ_) es) (map injL P ++ map injR ys)
      Perm.↭ map injL P ++ map injR (pe-stackK es ys)
  KBraid es P ys =
    subst (Perm._↭ (map injL P ++ map injR (pe-stackK es ys)))
          (sym (cong proj₁ (proj₁ (proj₂ (proj₂ (KBraid-data es P ys))))))
          (proj₂ (proj₂ (proj₂ (KBraid-data es P ys))))

  -- The K-side factorization target: the clean `(id {prefix} ⊗₁ Kterm)`
  -- (`KClean`) followed by the K-prepend braid `pvlC (↭-sym KBraid)` carrying
  -- the clean codomain back to the actual mixed-run codomain.  (Mirror of
  -- `GFactored` plus the wrinkle braid that the assembly later absorbs.)
  KFactored
    : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injL P ++ map injR ys)))
              (unflatten (map C.vlab
                 (pe-stackC (map (G.nE ↑ʳ_) es) (map injL P ++ map injR ys))))
  KFactored es P ys =
    pvlC (Perm.↭-sym (KBraid es P ys)) ∘ KClean es P ys

  ------------------------------------------------------------------------
  -- ### Permute functor helpers for the σ-in→pvl reconciliation (step 3).
  --
  -- `pvlC` is a ↭-functor for the SMART `↭-trans` too (not just the raw
  -- `Perm.trans` constructor): both reduce the `refl`-cases the same way.

  -- `pvlC` sends smart `↭-trans` to `∘` (by case analysis on the refl-cases).
  pvlC-↭trans
    : ∀ {as bs cs : List (Fin C.nV)} (p : as Perm.↭ bs) (q : bs Perm.↭ cs)
    → pvlC (Perm.↭-trans p q) ≈Term pvlC q ∘ pvlC p
  pvlC-↭trans Perm.refl q = ≈-Term-sym idʳ
  pvlC-↭trans (Perm.prep x p) Perm.refl = ≈-Term-sym idˡ
  pvlC-↭trans (Perm.prep x p) (Perm.prep y q) = ≈-Term-refl
  pvlC-↭trans (Perm.prep x p) (Perm.swap y z q) = ≈-Term-refl
  pvlC-↭trans (Perm.prep x p) (Perm.trans q₁ q₂) = ≈-Term-refl
  pvlC-↭trans (Perm.swap x y p) Perm.refl = ≈-Term-sym idˡ
  pvlC-↭trans (Perm.swap x y p) (Perm.prep z q) = ≈-Term-refl
  pvlC-↭trans (Perm.swap x y p) (Perm.swap z w q) = ≈-Term-refl
  pvlC-↭trans (Perm.swap x y p) (Perm.trans q₁ q₂) = ≈-Term-refl
  pvlC-↭trans (Perm.trans p₁ p₂) Perm.refl = ≈-Term-sym idˡ
  pvlC-↭trans (Perm.trans p₁ p₂) (Perm.prep z q) = ≈-Term-refl
  pvlC-↭trans (Perm.trans p₁ p₂) (Perm.swap z w q) = ≈-Term-refl
  pvlC-↭trans (Perm.trans p₁ p₂) (Perm.trans q₁ q₂) = ≈-Term-refl

  -- `pvlC (↭-reflexive eq)` is a `subst`-id codomain bridge (`subst-id-cod`).
  pvlC-reflexive-cod
    : ∀ {as bs : List (Fin C.nV)} (eq : as ≡ bs)
    → pvlC (Perm.↭-reflexive eq)
      ≈Term subst (λ z → HomTerm (unflatten (map C.vlab as)) (unflatten (map C.vlab z)))
                  eq (id {unflatten (map C.vlab as)})
  pvlC-reflexive-cod refl = ≈-Term-refl

  -- `↭-sym (↭-reflexive eq) ≡ ↭-reflexive (sym eq)`.
  sym-reflexive
    : ∀ {as bs : List (Fin C.nV)} (eq : as ≡ bs)
    → Perm.↭-sym (Perm.↭-reflexive eq) ≡ Perm.↭-reflexive (sym eq)
  sym-reflexive refl = refl

  -- `subst`-id codomain bridge over `map C.vlab`.
  sidC : ∀ {as bs : List (Fin C.nV)} → as ≡ bs
       → HomTerm (unflatten (map C.vlab as)) (unflatten (map C.vlab bs))
  sidC {as} eq =
    subst (λ z → HomTerm (unflatten (map C.vlab as)) (unflatten (map C.vlab z)))
          eq (id {unflatten (map C.vlab as)})

  ------------------------------------------------------------------------
  -- ### Shared subst-id (`sidX`) machinery, hoisted out of `Sin`/`Sout`
  -- (which each used a verbatim copy).  A canonical subst-id morphism `sidX`
  -- (codomain transport of `id` over `unflatten`) into which
  -- `sdd`/`scod`/`sidC` all collapse; it composes along `trans` and is unique
  -- (by `objUIP`).  Plus the dom/cod subst-id self-cancellations.

  sidX : ∀ {a b : List X} → a ≡ b → HomTerm (unflatten a) (unflatten b)
  sidX {a} e = subst (λ z → HomTerm (unflatten a) (unflatten z)) e id

  sidX-∘ : ∀ {a b c : List X} (p : a ≡ b) (q : b ≡ c)
         → sidX q ∘ sidX p ≈Term sidX (trans p q)
  sidX-∘ refl refl = idˡ

  sidX₂ : ∀ {a b : List X} (e : a ≡ b)
        → sidX e ≡ subst₂ HomTerm refl (cong unflatten e) (id {unflatten a})
  sidX₂ refl = refl

  sidX-irrel : ∀ {a b : List X} (e e' : a ≡ b) → sidX e ≈Term sidX e'
  sidX-irrel e e' =
    ≈-Term-trans (≡⇒≈Term (sidX₂ e))
      (≈-Term-trans (subst₂-HomTerm-irrel objUIP refl refl
                       (cong unflatten e) (cong unflatten e') id)
                    (≡⇒≈Term (sym (sidX₂ e'))))

  -- conversions into `sidX`.
  scod→sidX : ∀ {c d : List X} (q : c ≡ d) → BoxAssoc.subst-id-cod q ≈Term sidX q
  scod→sidX refl = ≈-Term-refl

  sdd→sidX : ∀ {a b : List X} (p : a ≡ b) → BoxAssoc.subst-id-dom p ≈Term sidX (sym p)
  sdd→sidX refl = ≈-Term-refl

  sidC→sidX : ∀ {a b : List (Fin C.nV)} (q : a ≡ b)
            → sidC q ≈Term sidX (cong (map C.vlab) q)
  sidC→sidX refl = ≈-Term-refl

  -- A subst-id over `unflatten` (domain side) self-cancels with its `sym`.
  sid-self-cancelᵈ : ∀ {a b : List X} (e : a ≡ b)
    → BoxAssoc.subst-id-dom e ∘ BoxAssoc.subst-id-dom (sym e) ≈Term id
  sid-self-cancelᵈ refl = idˡ

  -- A subst-id over `unflatten` (codomain side) self-cancels with its `sym`.
  sid-self-cancelᶜ : ∀ {a b : List X} (e : a ≡ b)
    → BoxAssoc.subst-id-cod e ∘ BoxAssoc.subst-id-cod (sym e) ≈Term id
  sid-self-cancelᶜ refl = idˡ

  -- `pvlC (shifts)` decomposed into the two `++-assoc` bridges and the
  -- `app-swap` (= `++⁺ʳ rgBlk (++-comm eiBlk Pblk)`) front-swap.
  pvlC-shifts
    : ∀ (eiBlk Pblk rgBlk : List (Fin C.nV))
    → pvlC (PermProp.shifts eiBlk Pblk {rgBlk})
      ≈Term sidC (++-assoc Pblk eiBlk rgBlk)
            ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
            ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
  pvlC-shifts eiBlk Pblk rgBlk = begin
      pvlC (PermProp.shifts eiBlk Pblk {rgBlk})
        ≈⟨ pvlC-↭trans A (Perm.↭-trans B (Perm.↭-trans C Perm.refl)) ⟩
      pvlC (Perm.↭-trans B (Perm.↭-trans C Perm.refl)) ∘ pvlC A
        ≈⟨ pvlC-↭trans B (Perm.↭-trans C Perm.refl) ⟩∘⟨refl ⟩
      (pvlC (Perm.↭-trans C Perm.refl) ∘ pvlC B) ∘ pvlC A
        ≈⟨ (pvlC-↭trans C Perm.refl ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((pvlC (Perm.refl {xs = Pblk ++ (eiBlk ++ rgBlk)}) ∘ pvlC C) ∘ pvlC B) ∘ pvlC A
        ≈⟨ (idˡ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (pvlC C ∘ pvlC B) ∘ pvlC A
        ≈⟨ FM.assoc ⟩
      pvlC C ∘ (pvlC B ∘ pvlC A)
        ≈⟨ pvlC-reflexive-cod (++-assoc Pblk eiBlk rgBlk) ⟩∘⟨ (refl⟩∘⟨ pvlC-A-eq) ⟩
      sidC (++-assoc Pblk eiBlk rgBlk)
        ∘ (pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
           ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))) ∎
    where
      A = Perm.↭-sym (Perm.↭-reflexive (++-assoc eiBlk Pblk rgBlk))
      B = PermProp.++⁺ʳ rgBlk (PermProp.++-comm eiBlk Pblk)
      C = Perm.↭-reflexive (++-assoc Pblk eiBlk rgBlk)

      pvlC-A-eq : pvlC A ≈Term sidC (sym (++-assoc eiBlk Pblk rgBlk))
      pvlC-A-eq =
        ≈-Term-trans (≡⇒≈Term (cong pvlC (sym-reflexive (++-assoc eiBlk Pblk rgBlk))))
                     (pvlC-reflexive-cod (sym (++-assoc eiBlk Pblk rgBlk)))

  ------------------------------------------------------------------------
  -- ### Infrastructure for `σin-as-pvl` — box-braid's `σ-in` (at `map C.vlab`
  -- IMAGE block args) as the `BTC.uf++`-framed `pvlC` of the block-shift
  -- permutation `shifts`.
  --
  -- The σ-mirror bridge: box-braid's input braid `σ-in` — the explicit
  -- `(σ ⊗ id)`-conjugate that moves the front block `einR` past the prefix
  -- `P` (carrying the residual `rest`) — equals
  -- `from(uf++ P (einR++rest)) ∘ pvl(shifts einR P rest)`.  PATH 2 plan (the
  -- PUBLIC vlab lemmas, NO raw private slide): `c-iso-assoc-from` reassociates
  -- σ-in's right-nested `unflatten-++-≅` views into BNV's left-nested `view≅`
  -- shape, `BNV.σ-frame-app-from` collapses the framed `(σ ⊗ id)` core into
  -- `pvl (app-swap)`, and `pvlC-shifts` reconciles `app-swap` to `shifts`.
  --
  -- The permute side (`pvlC-↭trans`, `pvlC-reflexive-cod`, `sym-reflexive`,
  -- `pvlC-shifts`) and the framing bridge `view-from-raw` (which re-expresses
  -- `from (view≅ A B C)` via the raw `unflatten-++-≅` isos + the two
  -- `map-++ C.vlab` subst-id conjugators) are PROVEN below.

  -- σ-in's raw framing-iso abbreviations, at the `map C.vlab` images.
  private
    rawTo₀ : (a b : List X) → HomTerm (unflatten a ⊗₀ unflatten b) (unflatten (a ++ b))
    rawTo₀ a b = _≅_.to (unflatten-++-≅ a b)

    rawFrom₀ : (a b : List X) → HomTerm (unflatten (a ++ b)) (unflatten a ⊗₀ unflatten b)
    rawFrom₀ a b = _≅_.from (unflatten-++-≅ a b)

    -- domain-only subst (codomain `refl`) is right-conjugation by subst-id-dom,
    -- for an ARBITRARY codomain object `Z` (e.g. a tensor — unlike
    -- `subst₂-as-conj`, whose codomain must be `unflatten`-of-a-list).
    subst-dom-conj
      : ∀ {a b : List X} {Z : ObjTerm} (p : a ≡ b) (t : HomTerm (unflatten a) Z)
      → subst₂ HomTerm (cong unflatten p) refl t
        ≈Term t ∘ BoxAssoc.subst-id-dom p
    subst-dom-conj refl t = ≈-Term-sym idʳ

  -- `from (view≅ A B C)` expressed via the raw `unflatten-++-≅` isos, with the
  -- two `map-++ C.vlab` domain reconciliations made explicit as subst-id
  -- conjugators (from `from-BTC` + `subst₂-as-conj`).  The two view-`from`
  -- factors are `(from(uf++ A B) ⊗ id) ∘ from(uf++ (A++B) C)`.
  view-from-raw
    : ∀ (A B Cc : List (Fin C.nV))
    → _≅_.from (BNV.view≅ C.vlab A B Cc)
      ≈Term (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id {unflatten (map C.vlab Cc)})
            ∘ (BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B))
                 ⊗₁ id {unflatten (map C.vlab Cc)})
            ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
               ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
  view-from-raw A B Cc = begin
      _≅_.from (BNV.view≅ C.vlab A B Cc)
        ≈⟨ vfr-unfold ⟩
      (_≅_.from (BTC.uf++ A B) ⊗₁ id {unflatten (map C.vlab Cc)})
        ∘ _≅_.from (BTC.uf++ (A ++ B) Cc)
        ≈⟨ ⊗-resp-≈ (≡⇒≈Term (from-BTC A B)) ≈-Term-refl ⟩∘⟨ ≡⇒≈Term (from-BTC (A ++ B) Cc) ⟩
      (subst₂ HomTerm (cong unflatten (sym (map-++ C.vlab A B))) refl
                (rawFrom₀ (map C.vlab A) (map C.vlab B)) ⊗₁ id)
        ∘ subst₂ HomTerm (cong unflatten (sym (map-++ C.vlab (A ++ B) Cc))) refl
                (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ≈⟨ ⊗-resp-≈ (subst-dom-conj (sym (map-++ C.vlab A B))
                       (rawFrom₀ (map C.vlab A) (map C.vlab B))) ≈-Term-refl
           ⟩∘⟨ subst-dom-conj (sym (map-++ C.vlab (A ++ B) Cc))
                 (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)) ⟩
      ((rawFrom₀ (map C.vlab A) (map C.vlab B)
         ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B))) ⊗₁ id)
        ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl ⟩
      (((rawFrom₀ (map C.vlab A) (map C.vlab B)
          ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B))) ) ⊗₁ (id ∘ id))
        ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
      ((rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
         ∘ (BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B)) ⊗₁ id))
        ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ FM.assoc ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ (BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B)) ⊗₁ id)
        ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc))) ∎
    where
      vfr-unfold
        : _≅_.from (BNV.view≅ C.vlab A B Cc)
          ≈Term (_≅_.from (BTC.uf++ A B) ⊗₁ id {unflatten (map C.vlab Cc)})
                ∘ _≅_.from (BTC.uf++ (A ++ B) Cc)
      vfr-unfold = ≈-Term-refl

  -- `rawFrom₀ (map (A++B)) (map C)` re-expressed with the first block split
  -- into `map A ++ map B` (the `map-++ C.vlab A B` block-1 reconciliation),
  -- via `from-blk1`.  (Pushes the `subst-id-dom (sym map-++)` conjugator in
  -- `view-from-raw` through the iso onto the raw first-block-split form.)
  rawFrom-blk1-split
    : ∀ (A B Cc : List (Fin C.nV))
    → (BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B)) ⊗₁ id {unflatten (map C.vlab Cc)})
        ∘ rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
      ≈Term rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
            ∘ BoxAssoc.subst-id-dom (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
  rawFrom-blk1-split A B Cc = lemma (sym (map-++ C.vlab A B))
    where
      lemma
        : ∀ {Lsplit Lwhole : List X} (e : Lsplit ≡ Lwhole)
        → (BoxAssoc.subst-id-dom e ⊗₁ id {unflatten (map C.vlab Cc)})
            ∘ rawFrom₀ Lwhole (map C.vlab Cc)
          ≈Term rawFrom₀ Lsplit (map C.vlab Cc)
                ∘ BoxAssoc.subst-id-dom (cong (_++ map C.vlab Cc) e)
      lemma {Lsplit} refl = begin
          (id {unflatten Lsplit} ⊗₁ id {unflatten (map C.vlab Cc)})
            ∘ rawFrom₀ Lsplit (map C.vlab Cc)
            ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
          id ∘ rawFrom₀ Lsplit (map C.vlab Cc)
            ≈⟨ idˡ ⟩
          rawFrom₀ Lsplit (map C.vlab Cc)
            ≈⟨ ≈-Term-sym idʳ ⟩
          rawFrom₀ Lsplit (map C.vlab Cc) ∘ id ∎

  -- two subst-id-doms compose into one subst-id-dom over `trans`.
  private
    sid-dom-∘
      : ∀ {a b c : List X} (p : a ≡ b) (q : b ≡ c)
      → BoxAssoc.subst-id-dom p ∘ BoxAssoc.subst-id-dom q
        ≈Term BoxAssoc.subst-id-dom (trans p q)
    sid-dom-∘ refl refl = idˡ

  -- `from (view≅ A B C)` = the RAW left-nested view `from`
  -- `(rawFrom₀(map A,map B) ⊗ id) ∘ rawFrom₀(map A++map B, map C)` precomposed
  -- with a single subst-id-dom over the combined outer `map-++` reconciliation.
  view-from-raw-clean
    : ∀ (A B Cc : List (Fin C.nV))
    → _≅_.from (BNV.view≅ C.vlab A B Cc)
      ≈Term ((rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id {unflatten (map C.vlab Cc)})
             ∘ rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
            ∘ BoxAssoc.subst-id-dom
                (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                       (sym (map-++ C.vlab (A ++ B) Cc)))
  view-from-raw-clean A B Cc = begin
      _≅_.from (BNV.view≅ C.vlab A B Cc)
        ≈⟨ view-from-raw A B Cc ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ (BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B)) ⊗₁ id)
        ∘ (rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ ((BoxAssoc.subst-id-dom (sym (map-++ C.vlab A B)) ⊗₁ id)
           ∘ rawFrom₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc))
        ≈⟨ refl⟩∘⟨ rawFrom-blk1-split A B Cc ⟩∘⟨refl ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ (rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
           ∘ BoxAssoc.subst-id-dom (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B))))
        ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc))
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
        ∘ (BoxAssoc.subst-id-dom (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
           ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sid-dom-∘ (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                              (sym (map-++ C.vlab (A ++ B) Cc)) ⟩
      (rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
        ∘ BoxAssoc.subst-id-dom
            (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                   (sym (map-++ C.vlab (A ++ B) Cc)))
        ≈⟨ FM.sym-assoc ⟩
      ((rawFrom₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ∘ rawFrom₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
        ∘ BoxAssoc.subst-id-dom
            (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                   (sym (map-++ C.vlab (A ++ B) Cc))) ∎

  ------------------------------------------------------------------------
  -- ### `to`-direction duals of `view-from-raw[-clean]`, for `σout-as-pvl`.

  -- codomain-only subst (domain `refl`) is left-conjugation by subst-id-cod,
  -- for an ARBITRARY domain object `Z` (mirror of `subst-dom-conj`).
  private
    subst-cod-conj
      : ∀ {c d : List X} {Z : ObjTerm} (q : c ≡ d) (t : HomTerm Z (unflatten c))
      → subst₂ HomTerm refl (cong unflatten q) t
        ≈Term BoxAssoc.subst-id-cod q ∘ t
    subst-cod-conj refl t = ≈-Term-sym idˡ

  -- `to (view≅ A B C)` expressed via the raw `unflatten-++-≅` isos, with the
  -- two `map-++ C.vlab` codomain reconciliations made explicit as subst-id
  -- conjugators (from `to-BTC` + `subst₂-as-conj`).  The two view-`to`
  -- factors are `to(uf++ (A++B) C) ∘ (to(uf++ A B) ⊗ id)`.
  view-to-raw
    : ∀ (A B Cc : List (Fin C.nV))
    → _≅_.to (BNV.view≅ C.vlab A B Cc)
      ≈Term (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
              ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
            ∘ (BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id {unflatten (map C.vlab Cc)})
            ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id {unflatten (map C.vlab Cc)})
  view-to-raw A B Cc = begin
      _≅_.to (BNV.view≅ C.vlab A B Cc)
        ≈⟨ vtr-unfold ⟩
      _≅_.to (BTC.uf++ (A ++ B) Cc)
        ∘ (_≅_.to (BTC.uf++ A B) ⊗₁ id {unflatten (map C.vlab Cc)})
        ≈⟨ ≡⇒≈Term (to-BTC (A ++ B) Cc) ⟩∘⟨ ⊗-resp-≈ (≡⇒≈Term (to-BTC A B)) ≈-Term-refl ⟩
      subst₂ HomTerm refl (cong unflatten (sym (map-++ C.vlab (A ++ B) Cc)))
              (rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ (subst₂ HomTerm refl (cong unflatten (sym (map-++ C.vlab A B)))
                  (rawTo₀ (map C.vlab A) (map C.vlab B)) ⊗₁ id)
        ≈⟨ subst-cod-conj (sym (map-++ C.vlab (A ++ B) Cc))
             (rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
           ⟩∘⟨ ⊗-resp-≈ (subst-cod-conj (sym (map-++ C.vlab A B))
                           (rawTo₀ (map C.vlab A) (map C.vlab B))) ≈-Term-refl ⟩
      (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
         ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ ((BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B))
            ∘ rawTo₀ (map C.vlab A) (map C.vlab B)) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩
      (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
         ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ ((BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B))
            ∘ rawTo₀ (map C.vlab A) (map C.vlab B)) ⊗₁ (id ∘ id))
        ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
      (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
         ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ ((BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id)
           ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)) ∎
    where
      vtr-unfold
        : _≅_.to (BNV.view≅ C.vlab A B Cc)
          ≈Term _≅_.to (BTC.uf++ (A ++ B) Cc)
                ∘ (_≅_.to (BTC.uf++ A B) ⊗₁ id {unflatten (map C.vlab Cc)})
      vtr-unfold = ≈-Term-refl

  -- `to(uf++ (A++B) C) ∘ (scod(sym map-++ A B) ⊗ id)` (the cod-bridge that
  -- re-splits block-1) pushed through the raw `to` onto the first-block-split
  -- form `to(mapA++mapB, C)`, leaving a single outer cod-bridge (mirror of
  -- `rawFrom-blk1-split`).
  rawTo-blk1-split
    : ∀ (A B Cc : List (Fin C.nV))
    → rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
        ∘ (BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id {unflatten (map C.vlab Cc)})
      ≈Term BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
            ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
  rawTo-blk1-split A B Cc = lemma (sym (map-++ C.vlab A B))
    where
      lemma
        : ∀ {Lsplit Lwhole : List X} (e : Lsplit ≡ Lwhole)
        → rawTo₀ Lwhole (map C.vlab Cc)
            ∘ (BoxAssoc.subst-id-cod e ⊗₁ id {unflatten (map C.vlab Cc)})
          ≈Term BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) e)
                ∘ rawTo₀ Lsplit (map C.vlab Cc)
      lemma {Lsplit} refl = begin
          rawTo₀ Lsplit (map C.vlab Cc)
            ∘ (id {unflatten Lsplit} ⊗₁ id {unflatten (map C.vlab Cc)})
            ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩
          rawTo₀ Lsplit (map C.vlab Cc) ∘ id
            ≈⟨ idʳ ⟩
          rawTo₀ Lsplit (map C.vlab Cc)
            ≈⟨ ≈-Term-sym idˡ ⟩
          id ∘ rawTo₀ Lsplit (map C.vlab Cc) ∎

  -- two subst-id-cods compose into one subst-id-cod over `trans`.
  private
    sid-cod-∘
      : ∀ {a b c : List X} (p : a ≡ b) (q : b ≡ c)
      → BoxAssoc.subst-id-cod q ∘ BoxAssoc.subst-id-cod p
        ≈Term BoxAssoc.subst-id-cod (trans p q)
    sid-cod-∘ refl refl = idˡ

  -- `to (view≅ A B C)` = the RAW left-nested view `to`
  -- `rawTo₀(mapA++mapB, mapC) ∘ (rawTo₀(map A,map B) ⊗ id)` POST-composed
  -- with a single subst-id-cod over the combined outer `map-++` reconciliation
  -- (mirror of `view-from-raw-clean`).
  view-to-raw-clean
    : ∀ (A B Cc : List (Fin C.nV))
    → _≅_.to (BNV.view≅ C.vlab A B Cc)
      ≈Term BoxAssoc.subst-id-cod
              (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                     (sym (map-++ C.vlab (A ++ B) Cc)))
            ∘ (rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
               ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id {unflatten (map C.vlab Cc)}))
  view-to-raw-clean A B Cc = begin
      _≅_.to (BNV.view≅ C.vlab A B Cc)
        ≈⟨ view-to-raw A B Cc ⟩
      (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
         ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc))
        ∘ (BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id)
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        -- bring `to(mapA++B,C) ∘ (scod(sym map-++ A B) ⊗ id)` adjacent.
        ≈⟨ FM.assoc ⟩
      BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
        ∘ (BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id)
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ (rawTo₀ (map C.vlab (A ++ B)) (map C.vlab Cc)
           ∘ (BoxAssoc.subst-id-cod (sym (map-++ C.vlab A B)) ⊗₁ id))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        -- push the block-1 cod-bridge through the raw `to` (rawTo-blk1-split).
        ≈⟨ refl⟩∘⟨ rawTo-blk1-split A B Cc ⟩∘⟨refl ⟩
      BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ (BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
           ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        -- merge the two leading cod-bridges into one over `trans`.
        ≈⟨ FM.sym-assoc ⟩
      (BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ (BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
           ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
      ((BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B))))
        ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ≈⟨ (sid-cod-∘ (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
                      (sym (map-++ C.vlab (A ++ B) Cc)) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (BoxAssoc.subst-id-cod
        (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
               (sym (map-++ C.vlab (A ++ B) Cc)))
        ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
        ≈⟨ FM.assoc ⟩
      BoxAssoc.subst-id-cod
        (trans (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
               (sym (map-++ C.vlab (A ++ B) Cc)))
        ∘ (rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc)
           ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)) ∎

  ------------------------------------------------------------------------
  -- ### `σin-as-pvl` — the final lemma.  box-braid's input braid `σ-in`,
  -- inlined at the `map C.vlab` block images, equals the `BTC.uf++`-framed
  -- `pvlC` of the block-shift permutation `shifts eiBlk Pblk rgBlk`.
  --
  -- The σ-in expression is reframed (via `subst₂`) onto the `map C.vlab (·)`
  -- endpoints so the RHS is the pristine `from(uf++) ∘ pvlC(shifts)`.

  module Sin (eiBlk Pblk rgBlk : List (Fin C.nV)) where
    eL = map C.vlab eiBlk
    pL = map C.vlab Pblk
    rL = map C.vlab rgBlk
    Up = unflatten pL
    Ue = unflatten eL
    Ur = unflatten rL

    rTo : (a b : List X) → HomTerm (unflatten a ⊗₀ unflatten b) (unflatten (a ++ b))
    rTo = rawTo₀
    rFrom : (a b : List X) → HomTerm (unflatten (a ++ b)) (unflatten a ⊗₀ unflatten b)
    rFrom = rawFrom₀

    -- inlined σ-in (raw framing on the map-images), the box-braid definition.
    σ-in-raw : HomTerm (unflatten (eL ++ (pL ++ rL))) (Up ⊗₀ unflatten (eL ++ rL))
    σ-in-raw =
        (id {Up} ⊗₁ rTo eL rL)
      ∘ α⇒ {Up} {Ue} {Ur}
      ∘ (σ {Ue} {Up} ⊗₁ id {Ur})
      ∘ α⇐ {Ue} {Up} {Ur}
      ∘ (id {Ue} ⊗₁ rFrom pL rL)
      ∘ rFrom eL (pL ++ rL)

    -- cif, with the trailing subst reassociated to the outside.
    cif-assoc :
      α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL
      ≈Term ((id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL))
            ∘ BoxAssoc.subst-id-cod (++-assoc eL pL rL)
    cif-assoc = begin
        α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL
          ≈⟨ c-iso-assoc-from eL pL rL ⟩
        (id {Ue} ⊗₁ rFrom pL rL)
          ∘ rFrom eL (pL ++ rL)
          ∘ BoxAssoc.subst-id-cod (++-assoc eL pL rL)
          ≈⟨ FM.sym-assoc ⟩
        ((id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL))
          ∘ BoxAssoc.subst-id-cod (++-assoc eL pL rL) ∎

    -- the raw input view-from (left-nested), recovered from σ-in's tail.
    in-frame :
      α⇐ {Ue} {Up} {Ur} ∘ (id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL)
      ≈Term ((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
            ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
    in-frame = begin
        α⇐ {Ue} {Up} {Ur} ∘ (id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL)
          ≈⟨ refl⟩∘⟨ tail-eq ⟩
        α⇐ {Ue} {Up} {Ur}
          ∘ (α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈⟨ FM.sym-assoc ⟩
        (α⇐ {Ue} {Up} {Ur}
          ∘ (α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL))
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
        ((α⇐ {Ue} {Up} {Ur} ∘ α⇒ {Ue} {Up} {Ur})
          ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (id ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈⟨ idˡ ⟩∘⟨refl ⟩
        ((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)) ∎
      where
        -- `(id⊗rFrom)∘rFrom ≈ (α⇒∘(rFrom⊗id)∘rFrom) ∘ scod(sym ++-assoc)`.
        tail-eq :
          (id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL)
          ≈Term (α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
        tail-eq = begin
            (id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL)
              ≈⟨ ≈-Term-sym idʳ ⟩
            ((id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL)) ∘ id
              ≈⟨ refl⟩∘⟨ ≈-Term-sym (sid-self-cancelᶜ (++-assoc eL pL rL)) ⟩
            ((id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL))
              ∘ (BoxAssoc.subst-id-cod (++-assoc eL pL rL)
                 ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
              ≈⟨ FM.sym-assoc ⟩
            (((id {Ue} ⊗₁ rFrom pL rL) ∘ rFrom eL (pL ++ rL))
              ∘ BoxAssoc.subst-id-cod (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              ≈⟨ ≈-Term-sym cif-assoc ⟩∘⟨refl ⟩
            (α⇒ {Ue} {Up} {Ur} ∘ (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
              ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)) ∎

    -- combined outer `map-++` reconciliations for the two view frames.
    comb-in : (eL ++ pL) ++ rL ≡ map C.vlab ((eiBlk ++ Pblk) ++ rgBlk)
    comb-in = trans (cong (_++ rL) (sym (map-++ C.vlab eiBlk Pblk)))
                    (sym (map-++ C.vlab (eiBlk ++ Pblk) rgBlk))

    comb-out : (pL ++ eL) ++ rL ≡ map C.vlab ((Pblk ++ eiBlk) ++ rgBlk)
    comb-out = trans (cong (_++ rL) (sym (map-++ C.vlab Pblk eiBlk)))
                     (sym (map-++ C.vlab (Pblk ++ eiBlk) rgBlk))

    -- the raw left-nested input view-from, expressed via `from(view≅)`.
    raw-as-view-in :
      (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL
      ≈Term _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
            ∘ BoxAssoc.subst-id-dom (sym comb-in)
    raw-as-view-in = begin
        (rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL
          ≈⟨ ≈-Term-sym idʳ ⟩
        ((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL) ∘ id
          ≈⟨ refl⟩∘⟨ ≈-Term-sym (sid-self-cancelᵈ comb-in) ⟩
        ((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ (BoxAssoc.subst-id-dom comb-in ∘ BoxAssoc.subst-id-dom (sym comb-in))
          ≈⟨ FM.sym-assoc ⟩
        (((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
          ∘ BoxAssoc.subst-id-dom comb-in)
          ∘ BoxAssoc.subst-id-dom (sym comb-in)
          ≈⟨ ≈-Term-sym (view-from-raw-clean eiBlk Pblk rgBlk) ⟩∘⟨refl ⟩
        _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
          ∘ BoxAssoc.subst-id-dom (sym comb-in) ∎

    -- cif at `pL eL rL`, trailing subst reassociated out.
    cif-assoc-out :
      α⇒ {Up} {Ue} {Ur} ∘ (rFrom pL eL ⊗₁ id {Ur}) ∘ rFrom (pL ++ eL) rL
      ≈Term ((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
            ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL)
    cif-assoc-out = begin
        α⇒ {Up} {Ue} {Ur} ∘ (rFrom pL eL ⊗₁ id {Ur}) ∘ rFrom (pL ++ eL) rL
          ≈⟨ c-iso-assoc-from pL eL rL ⟩
        (id {Up} ⊗₁ rFrom eL rL)
          ∘ rFrom pL (eL ++ rL)
          ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL)
          ≈⟨ FM.sym-assoc ⟩
        ((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
          ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∎

    -- the OUTPUT frame collapse: σ-in's leading `(id⊗rTo)∘α⇒`, composed onto
    -- the output view-from, telescopes to the single-block `rFrom pL (eL++rL)`.
    out-frame :
      (id {Up} ⊗₁ rTo eL rL) ∘ α⇒ {Up} {Ue} {Ur}
        ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
      ≈Term (rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
            ∘ BoxAssoc.subst-id-dom comb-out
    out-frame = begin
        (id {Up} ⊗₁ rTo eL rL) ∘ α⇒ {Up} {Ue} {Ur}
          ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ view-from-raw-clean Pblk eiBlk rgBlk ⟩
        (id {Up} ⊗₁ rTo eL rL) ∘ α⇒ {Up} {Ue} {Ur}
          ∘ (((rFrom pL eL ⊗₁ id {Ur}) ∘ rFrom (pL ++ eL) rL)
             ∘ BoxAssoc.subst-id-dom comb-out)
          -- regroup so `α⇒ ∘ (rFrom⊗id) ∘ rFrom` is adjacent (peel sdd out).
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (α⇒ {Up} {Ue} {Ur} ∘ (rFrom pL eL ⊗₁ id {Ur}) ∘ rFrom (pL ++ eL) rL)
          ∘ BoxAssoc.subst-id-dom comb-out
          ≈⟨ refl⟩∘⟨ cif-assoc-out ⟩∘⟨refl ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
             ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
          ∘ BoxAssoc.subst-id-dom comb-out
          -- right-associate the trailing substs onto `rFrom pL (eL++rL)`.
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          -- collapse `(id⊗rTo) ∘ (id⊗rFrom) = id`.
          ≈⟨ FM.sym-assoc ⟩
        ((id {Up} ⊗₁ rTo eL rL) ∘ (id {Up} ⊗₁ rFrom eL rL))
          ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
        ((id {Up} ∘ id {Up}) ⊗₁ (rTo eL rL ∘ rFrom eL rL))
          ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ ⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ eL rL)) ⟩∘⟨refl ⟩
        (id {Up} ⊗₁ id {unflatten (eL ++ rL)})
          ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
        id ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ idˡ ⟩
        rFrom pL (eL ++ rL)
          ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out)
          ≈⟨ FM.sym-assoc ⟩
        (rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
          ∘ BoxAssoc.subst-id-dom comb-out ∎

    -- the assembled raw composite: σ-in chained through in-frame,
    -- raw-as-view-in, σ-frame-app-from, out-frame.
    sin-assembled :
      σ-in-raw
      ≈Term ((rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
             ∘ BoxAssoc.subst-id-dom comb-out)
            ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
            ∘ BoxAssoc.subst-id-dom (sym comb-in)
            ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
    sin-assembled = begin
        σ-in-raw
          -- (1) in-frame on the tail (`α⇐ ∘ (id⊗rFrom pL rL) ∘ rFrom eL (pL++rL)`).
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ in-frame ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ α⇒ {Up} {Ue} {Ur}
          ∘ (σ {Ue} {Up} ⊗₁ id {Ur})
          ∘ (((rFrom eL pL ⊗₁ id {Ur}) ∘ rFrom (eL ++ pL) rL)
             ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
          -- (2) raw-as-view-in on the left-nested input view.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ raw-as-view-in ⟩∘⟨refl ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ α⇒ {Up} {Ue} {Ur}
          ∘ (σ {Ue} {Up} ⊗₁ id {Ur})
          ∘ (_≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
             ∘ BoxAssoc.subst-id-dom (sym comb-in))
            ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          -- regroup so `(σ⊗id) ∘ from(view≅ ei P rg)` is adjacent.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ regroup-σ ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ α⇒ {Up} {Ue} {Ur}
          ∘ ((σ {Ue} {Up} ⊗₁ id {Ur}) ∘ _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk))
            ∘ BoxAssoc.subst-id-dom (sym comb-in)
            ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          -- (3) σ-frame-app-from.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ BNV.σ-frame-app-from C.vlab Pblk eiBlk rgBlk ⟩∘⟨refl ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ α⇒ {Up} {Ue} {Ur}
          ∘ (_≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
             ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk))
            ∘ BoxAssoc.subst-id-dom (sym comb-in)
            ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          -- regroup so `(id⊗rTo) ∘ α⇒ ∘ from(view≅ P ei rg)` is adjacent.
          ≈⟨ regroup-out ⟩
        ((id {Up} ⊗₁ rTo eL rL) ∘ α⇒ {Up} {Ue} {Ur}
          ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk))
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ BoxAssoc.subst-id-dom (sym comb-in)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          -- (4) out-frame.
          ≈⟨ out-frame ⟩∘⟨refl ⟩
        ((rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
          ∘ BoxAssoc.subst-id-dom comb-out)
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ BoxAssoc.subst-id-dom (sym comb-in)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)) ∎
      where
        -- regroup `(σ⊗id) ∘ (from(view≅) ∘ sdd) ∘ scod` so the σ-frame core is
        -- a single factor, trailing substs peeled out.
        regroup-σ :
          (σ {Ue} {Up} ⊗₁ id {Ur})
            ∘ (_≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
               ∘ BoxAssoc.subst-id-dom (sym comb-in))
              ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈Term ((σ {Ue} {Up} ⊗₁ id {Ur}) ∘ _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk))
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
        regroup-σ = begin
            (σ {Ue} {Up} ⊗₁ id {Ur})
              ∘ (_≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
                 ∘ BoxAssoc.subst-id-dom (sym comb-in))
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            (σ {Ue} {Up} ⊗₁ id {Ur})
              ∘ _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk)
              ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              ≈⟨ FM.sym-assoc ⟩
            ((σ {Ue} {Up} ⊗₁ id {Ur}) ∘ _≅_.from (BNV.view≅ C.vlab eiBlk Pblk rgBlk))
              ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)) ∎

        -- regroup `(id⊗rTo) ∘ α⇒ ∘ (from(view≅ P ei rg) ∘ pvlC) ∘ ...` so that
        -- `(id⊗rTo) ∘ α⇒ ∘ from(view≅ P ei rg)` is a single factor.
        regroup-out :
          (id {Up} ⊗₁ rTo eL rL)
            ∘ α⇒ {Up} {Ue} {Ur}
            ∘ (_≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
               ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk))
              ∘ BoxAssoc.subst-id-dom (sym comb-in)
              ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
          ≈Term ((id {Up} ⊗₁ rTo eL rL) ∘ α⇒ {Up} {Ue} {Ur}
                 ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk))
                ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
        regroup-out = begin
            (id {Up} ⊗₁ rTo eL rL)
              ∘ α⇒ {Up} {Ue} {Ur}
              ∘ (_≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
                 ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk))
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              -- peel the `pvlC ∘ sdd ∘ scod` tail out of the view-from factor.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            (id {Up} ⊗₁ rTo eL rL)
              ∘ α⇒ {Up} {Ue} {Ur}
              ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)
              ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            (id {Up} ⊗₁ rTo eL rL)
              ∘ (α⇒ {Up} {Ue} {Ur} ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk))
              ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
              ≈⟨ FM.sym-assoc ⟩
            ((id {Up} ⊗₁ rTo eL rL)
              ∘ (α⇒ {Up} {Ue} {Ur} ∘ _≅_.from (BNV.view≅ C.vlab Pblk eiBlk rgBlk)))
              ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
                ∘ BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)) ∎

    ----------------------------------------------------------------------
    -- ### Boundary reconciliation: the assembled raw composite vs the
    -- pristine `from(uf++) ∘ pvlC(shifts)` form.  Pure subst-id bookkeeping.

    -- domain reframe (σ-in's raw dom → `map`-image dom).
    dom-list : eL ++ (pL ++ rL) ≡ map C.vlab (eiBlk ++ (Pblk ++ rgBlk))
    dom-list = trans (cong (eL ++_) (sym (map-++ C.vlab Pblk rgBlk)))
                     (sym (map-++ C.vlab eiBlk (Pblk ++ rgBlk)))

    -- codomain reframe (σ-in's raw cod `Up ⊗ unflatten(eL++rL)` → tensor over
    -- the combined `map(eiBlk++rgBlk)`).
    cod-list : eL ++ rL ≡ map C.vlab (eiBlk ++ rgBlk)
    cod-list = sym (map-++ C.vlab eiBlk rgBlk)

    -- tensor-codomain subst-id morphism `Up ⊗ unflatten c → Up ⊗ unflatten d`.
    tcod : ∀ {c d : List X} → c ≡ d → HomTerm (Up ⊗₀ unflatten c) (Up ⊗₀ unflatten d)
    tcod {c} e = subst (λ z → HomTerm (Up ⊗₀ unflatten c) (Up ⊗₀ unflatten z)) e id

    -- combined domain bridge for `from(uf++ Pblk (eiBlk++rgBlk))`'s raw form
    -- (split the second block via `map-++`, then the outer `map-++`).
    dom-uf : pL ++ (eL ++ rL) ≡ map C.vlab (Pblk ++ (eiBlk ++ rgBlk))
    dom-uf = trans (cong (pL ++_) (sym (map-++ C.vlab eiBlk rgBlk)))
                   (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))

    -- the raw single-block `rawFrom₀ pL (map(ei++rg))` expressed via the raw
    -- `rawFrom₀ pL (eL++rL)`, conjugated by the `map-++ eiBlk rgBlk` split
    -- (`tcod` on the codomain, `subst-id-dom` on the inner domain).  `J` on
    -- `cod-list`.
    split-gen :
      ∀ {W : List X} (e : eL ++ rL ≡ W)
      → rFrom pL W
        ≈Term tcod e ∘ rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-dom (cong (pL ++_) e)
    split-gen refl = ≈-Term-sym (≈-Term-trans idˡ idʳ)

    split-eq :
      rFrom pL (map C.vlab (eiBlk ++ rgBlk))
      ≈Term tcod cod-list ∘ rFrom pL (eL ++ rL)
            ∘ BoxAssoc.subst-id-dom (cong (pL ++_) cod-list)
    split-eq = split-gen cod-list

    -- the BTC.uf++ output iso `from`, in raw subst-conjugated form.
    from-uf-raw : _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
                ≈Term tcod cod-list
                      ∘ rFrom pL (eL ++ rL)
                      ∘ BoxAssoc.subst-id-dom dom-uf
    from-uf-raw = begin
        _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
          ≈⟨ ≡⇒≈Term (from-BTC Pblk (eiBlk ++ rgBlk)) ⟩
        subst₂ HomTerm (cong unflatten (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))) refl
          (rFrom pL (map C.vlab (eiBlk ++ rgBlk)))
          ≈⟨ subst-dom-conj (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))
               (rFrom pL (map C.vlab (eiBlk ++ rgBlk))) ⟩
        rFrom pL (map C.vlab (eiBlk ++ rgBlk))
          ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))
          ≈⟨ split-eq ⟩∘⟨refl ⟩
        (tcod cod-list ∘ rFrom pL (eL ++ rL)
          ∘ BoxAssoc.subst-id-dom (cong (pL ++_) cod-list))
          ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))
          ≈⟨ FM.assoc ⟩
        tcod cod-list
          ∘ (rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-dom (cong (pL ++_) cod-list))
          ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        tcod cod-list
          ∘ rFrom pL (eL ++ rL)
          ∘ (BoxAssoc.subst-id-dom (cong (pL ++_) cod-list)
             ∘ BoxAssoc.subst-id-dom (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk))))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sid-dom-∘ (cong (pL ++_) cod-list)
                            (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk))) ⟩
        tcod cod-list
          ∘ rFrom pL (eL ++ rL)
          ∘ BoxAssoc.subst-id-dom (trans (cong (pL ++_) cod-list)
                                         (sym (map-++ C.vlab Pblk (eiBlk ++ rgBlk)))) ∎

    ----------------------------------------------------------------------
    -- ### subst-id morphisms as `subst₂ HomTerm _ _ id` (for uniqueness via
    -- `subst₂-HomTerm-irrel`).

    sdd₂ : ∀ {a b : List X} (p : a ≡ b)
         → BoxAssoc.subst-id-dom p ≡ subst₂ HomTerm (cong unflatten p) refl (id {unflatten a})
    sdd₂ refl = refl

    scod₂ : ∀ {c d : List X} (q : c ≡ d)
          → BoxAssoc.subst-id-cod q ≡ subst₂ HomTerm refl (cong unflatten q) (id {unflatten c})
    scod₂ refl = refl

    sidC₂ : ∀ {a b : List (Fin C.nV)} (q : a ≡ b)
          → sidC q ≡ subst₂ HomTerm refl (cong unflatten (cong (map C.vlab) q))
                            (id {unflatten (map C.vlab a)})
    sidC₂ refl = refl

    tcod₂ : ∀ {c d : List X} (q : c ≡ d)
          → tcod q ≡ subst₂ HomTerm refl (cong (Up ⊗₀_) (cong unflatten q))
                            (id {Up ⊗₀ unflatten c})
    tcod₂ refl = refl

    -- conjugation of σ-in-raw by the dom/cod reframes (cod over `Up ⊗ unflatten`).
    subst₂-conj-tensor :
      ∀ {a b : List X} {c d : List X} (p : a ≡ b) (q : c ≡ d)
        (t : HomTerm (unflatten a) (Up ⊗₀ unflatten c))
      → subst₂ HomTerm (cong unflatten p) (cong (Up ⊗₀_) (cong unflatten q)) t
        ≈Term tcod q ∘ t ∘ BoxAssoc.subst-id-dom p
    subst₂-conj-tensor refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)


    ----------------------------------------------------------------------
    -- ### The two boundary equalities (subst-id-morphism uniqueness).

    -- RIGHT of `pvlC(app-swap)`: the assembled input substs vs `shifts`' first
    -- bridge `sidC(sym(++-assoc eiBlk Pblk rgBlk))`.
    right-eq :
      (BoxAssoc.subst-id-dom (sym comb-in)
        ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
        ∘ BoxAssoc.subst-id-dom dom-list
      ≈Term sidC (sym (++-assoc eiBlk Pblk rgBlk))
    right-eq = begin
        (BoxAssoc.subst-id-dom (sym comb-in)
          ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
          ∘ BoxAssoc.subst-id-dom dom-list
          ≈⟨ (sdd→sidX (sym comb-in) ⟩∘⟨ scod→sidX (sym (++-assoc eL pL rL)))
             ⟩∘⟨ sdd→sidX dom-list ⟩
        (sidX (sym (sym comb-in)) ∘ sidX (sym (++-assoc eL pL rL)))
          ∘ sidX (sym dom-list)
          ≈⟨ sidX-∘ (sym (++-assoc eL pL rL)) (sym (sym comb-in)) ⟩∘⟨refl ⟩
        sidX (trans (sym (++-assoc eL pL rL)) (sym (sym comb-in)))
          ∘ sidX (sym dom-list)
          ≈⟨ sidX-∘ (sym dom-list) (trans (sym (++-assoc eL pL rL)) (sym (sym comb-in))) ⟩
        sidX (trans (sym dom-list) (trans (sym (++-assoc eL pL rL)) (sym (sym comb-in))))
          ≈⟨ sidX-irrel _ (cong (map C.vlab) (sym (++-assoc eiBlk Pblk rgBlk))) ⟩
        sidX (cong (map C.vlab) (sym (++-assoc eiBlk Pblk rgBlk)))
          ≈⟨ ≈-Term-sym (sidC→sidX (sym (++-assoc eiBlk Pblk rgBlk))) ⟩
        sidC (sym (++-assoc eiBlk Pblk rgBlk)) ∎

    -- LEFT of `pvlC(app-swap)`: the assembled output substs vs `shifts`' second
    -- bridge `sidC(++-assoc Pblk eiBlk rgBlk)`, modulo the shared `rFrom`.
    left-eq :
      (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out)
      ≈Term BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk)
    left-eq = begin
        BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out
          ≈⟨ scod→sidX (++-assoc pL eL rL) ⟩∘⟨ sdd→sidX comb-out ⟩
        sidX (++-assoc pL eL rL) ∘ sidX (sym comb-out)
          ≈⟨ sidX-∘ (sym comb-out) (++-assoc pL eL rL) ⟩
        sidX (trans (sym comb-out) (++-assoc pL eL rL))
          ≈⟨ sidX-irrel _ (trans (cong (map C.vlab) (++-assoc Pblk eiBlk rgBlk)) (sym dom-uf)) ⟩
        sidX (trans (cong (map C.vlab) (++-assoc Pblk eiBlk rgBlk)) (sym dom-uf))
          ≈⟨ ≈-Term-sym (sidX-∘ (cong (map C.vlab) (++-assoc Pblk eiBlk rgBlk)) (sym dom-uf)) ⟩
        sidX (sym dom-uf) ∘ sidX (cong (map C.vlab) (++-assoc Pblk eiBlk rgBlk))
          ≈⟨ ≈-Term-sym (sdd→sidX dom-uf) ⟩∘⟨ ≈-Term-sym (sidC→sidX (++-assoc Pblk eiBlk rgBlk)) ⟩
        BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk) ∎

    ----------------------------------------------------------------------
    -- ### The final lemma: box-braid's input braid `σ-in` (reframed onto the
    -- `map C.vlab (·)` endpoints) is the `BTC.uf++`-framed `pvlC` of `shifts`.
    σin-as-pvl :
      subst₂ HomTerm (cong unflatten dom-list)
                     (cong (Up ⊗₀_) (cong unflatten cod-list)) σ-in-raw
      ≈Term _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
            ∘ pvlC (PermProp.shifts eiBlk Pblk {rgBlk})
    σin-as-pvl = begin
        subst₂ HomTerm (cong unflatten dom-list)
                       (cong (Up ⊗₀_) (cong unflatten cod-list)) σ-in-raw
          ≈⟨ subst₂-conj-tensor dom-list cod-list σ-in-raw ⟩
        tcod cod-list ∘ σ-in-raw ∘ BoxAssoc.subst-id-dom dom-list
          ≈⟨ refl⟩∘⟨ sin-assembled ⟩∘⟨refl ⟩
        tcod cod-list
          ∘ (((rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
              ∘ BoxAssoc.subst-id-dom comb-out)
             ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
             ∘ BoxAssoc.subst-id-dom (sym comb-in)
             ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
          ∘ BoxAssoc.subst-id-dom dom-list
          -- pull the `tcod cod-list` into the leading `rFrom`-block, and the
          -- trailing `sdd dom-list` into the input-subst block.
          ≈⟨ regroup ⟩
        ((tcod cod-list ∘ rFrom pL (eL ++ rL))
          ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ ((BoxAssoc.subst-id-dom (sym comb-in)
              ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
             ∘ BoxAssoc.subst-id-dom dom-list)
          -- (LEFT) left-eq on the output substs; (RIGHT) right-eq on input substs.
          ≈⟨ (refl⟩∘⟨ left-eq) ⟩∘⟨ (refl⟩∘⟨ right-eq) ⟩
        ((tcod cod-list ∘ rFrom pL (eL ++ rL))
          ∘ (BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk)))
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
          -- reassemble the leading block into `from(uf++) ∘ sidC(++-assoc P ei rg)`.
          ≈⟨ reassemble-left ⟩
        (_≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk)) ∘ sidC (++-assoc Pblk eiBlk rgBlk))
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
          -- fold `sidC ∘ pvlC(app-swap) ∘ sidC` back into `pvlC(shifts)`.
          ≈⟨ FM.assoc ⟩
        _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
          ∘ sidC (++-assoc Pblk eiBlk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym (pvlC-shifts eiBlk Pblk rgBlk) ⟩
        _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
          ∘ pvlC (PermProp.shifts eiBlk Pblk {rgBlk}) ∎
      where
        cA = BoxAssoc.subst-id-cod (++-assoc pL eL rL)
        dCO = BoxAssoc.subst-id-dom comb-out
        pA = pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
        dCI = BoxAssoc.subst-id-dom (sym comb-in)
        cAs = BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL))
        dDL = BoxAssoc.subst-id-dom dom-list

        -- the big associativity regroup (pure ∘-reshuffle).
        regroup :
          tcod cod-list
            ∘ (((rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
                ∘ BoxAssoc.subst-id-dom comb-out)
               ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
               ∘ BoxAssoc.subst-id-dom (sym comb-in)
               ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
            ∘ BoxAssoc.subst-id-dom dom-list
          ≈Term ((tcod cod-list ∘ rFrom pL (eL ++ rL))
            ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
            ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
            ∘ ((BoxAssoc.subst-id-dom (sym comb-in)
                ∘ BoxAssoc.subst-id-cod (sym (++-assoc eL pL rL)))
               ∘ BoxAssoc.subst-id-dom dom-list)
        regroup = begin
            tcod cod-list
              ∘ (((rFrom pL (eL ++ rL) ∘ cA) ∘ dCO)
                 ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              -- bring `tcod` adjacent to the leading `(rFrom∘cA)∘dCO`.
              ≈⟨ FM.sym-assoc ⟩
            (tcod cod-list
              ∘ (((rFrom pL (eL ++ rL) ∘ cA) ∘ dCO)
                 ∘ pA ∘ dCI ∘ cAs))
              ∘ dDL
              ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
            ((tcod cod-list ∘ (((rFrom pL (eL ++ rL) ∘ cA) ∘ dCO)))
              ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              ≈⟨ (FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
            (((tcod cod-list ∘ ((rFrom pL (eL ++ rL) ∘ cA))) ∘ dCO)
              ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              ≈⟨ ((((FM.sym-assoc ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩∘⟨refl ⟩
            ((((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ cA) ∘ dCO)
              ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              -- cluster `((tcod∘rFrom)∘(cA∘dCO))` on the left.
              ≈⟨ (FM.assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
            (((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              -- now reassociate the whole `(LEFT ∘ (pA ∘ dCI ∘ cAs)) ∘ dDL`.
              ≈⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ ((pA ∘ dCI ∘ cAs) ∘ dDL)
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ ((dCI ∘ cAs) ∘ dDL)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ (dCI ∘ cAs ∘ dDL)
              -- re-cluster the input substs as `(dCI ∘ cAs) ∘ dDL`.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ ((dCI ∘ cAs) ∘ dDL) ∎

        reassemble-left :
          ((tcod cod-list ∘ rFrom pL (eL ++ rL))
            ∘ (BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk)))
            ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
            ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
          ≈Term (_≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk)) ∘ sidC (++-assoc Pblk eiBlk rgBlk))
            ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
            ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
        reassemble-left = left-block-eq ⟩∘⟨refl
          where
            left-block-eq :
              (tcod cod-list ∘ rFrom pL (eL ++ rL))
                ∘ (BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk))
              ≈Term _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
                    ∘ sidC (++-assoc Pblk eiBlk rgBlk)
            left-block-eq = begin
                (tcod cod-list ∘ rFrom pL (eL ++ rL))
                  ∘ (BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk))
                  ≈⟨ FM.assoc ⟩
                tcod cod-list ∘ rFrom pL (eL ++ rL)
                  ∘ (BoxAssoc.subst-id-dom dom-uf ∘ sidC (++-assoc Pblk eiBlk rgBlk))
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                tcod cod-list
                  ∘ (rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-dom dom-uf)
                  ∘ sidC (++-assoc Pblk eiBlk rgBlk)
                  ≈⟨ FM.sym-assoc ⟩
                (tcod cod-list ∘ (rFrom pL (eL ++ rL) ∘ BoxAssoc.subst-id-dom dom-uf))
                  ∘ sidC (++-assoc Pblk eiBlk rgBlk)
                  ≈⟨ ≈-Term-sym from-uf-raw ⟩∘⟨refl ⟩
                _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
                  ∘ sidC (++-assoc Pblk eiBlk rgBlk) ∎

  ------------------------------------------------------------------------
  -- ### `σout-as-pvl` — the DUAL of `σin-as-pvl`.  box-braid's OUTPUT braid
  -- `σ-out`, inlined at the `map C.vlab` block images, equals the
  -- `pvlC`-of-`shifts` POST-composed onto the `BTC.uf++` output iso `to`.
  --
  -- It is the vertical mirror of `module Sin`: dom↔cod, to↔from, α⇒↔α⇐ all
  -- swapped; the σ-frame core is collapsed by the `to`-orientation keystone
  -- `BNV.σ-frame-app-to′` (vs `σ-frame-app-from`), the views by the
  -- `to`-direction `view-to-raw[-clean]`, the reassociations by `c-iso-assoc-to`.

  module Sout (eoBlk Pblk rgBlk : List (Fin C.nV)) where
    eL = map C.vlab eoBlk
    pL = map C.vlab Pblk
    rL = map C.vlab rgBlk
    Up = unflatten pL
    Ue = unflatten eL
    Ur = unflatten rL

    rTo : (a b : List X) → HomTerm (unflatten a ⊗₀ unflatten b) (unflatten (a ++ b))
    rTo = rawTo₀
    rFrom : (a b : List X) → HomTerm (unflatten (a ++ b)) (unflatten a ⊗₀ unflatten b)
    rFrom = rawFrom₀

    -- inlined σ-out (raw framing on the map-images), the box-braid definition
    -- (with eoutR → eoBlk, P → Pblk, rest → rgBlk).
    σ-out-raw : HomTerm (Up ⊗₀ unflatten (eL ++ rL)) (unflatten (eL ++ (pL ++ rL)))
    σ-out-raw =
        rTo eL (pL ++ rL)
      ∘ (id {Ue} ⊗₁ rTo pL rL)
      ∘ α⇒ {Ue} {Up} {Ur}
      ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
      ∘ α⇐ {Up} {Ue} {Ur}
      ∘ (id {Up} ⊗₁ rFrom eL rL)

    -- `c-iso-assoc-to eL pL rL`, trailing subst reassociated to the right
    -- (dual of `Sin.cif-assoc-out`).
    cit-assoc-head :
      rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur}
      ≈Term BoxAssoc.subst-id-dom (++-assoc eL pL rL)
            ∘ (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL))
    cit-assoc-head = begin
        rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur}
          ≈⟨ BoxAssoc.c-iso-assoc-to eL pL rL ⟩
        BoxAssoc.subst-id-dom (++-assoc eL pL rL)
          ∘ (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL)) ∎

    -- the combined `map-++` codomain bridge of `view-to-raw-clean eoBlk Pblk rgBlk`.
    bridge-eo : (eL ++ pL) ++ rL ≡ map C.vlab ((eoBlk ++ Pblk) ++ rgBlk)
    bridge-eo = trans (cong (_++ rL) (sym (map-++ C.vlab eoBlk Pblk)))
                      (sym (map-++ C.vlab (eoBlk ++ Pblk) rgBlk))

    -- the raw left-nested output view-to, expressed via `to(view≅)` (dual of
    -- `Sin.raw-as-view-in`).  `to(view≅) = scod(bridge-eo) ∘ raw`, so
    -- `raw = scod(sym bridge-eo) ∘ to(view≅)`.
    raw-as-view-out :
      rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur})
      ≈Term BoxAssoc.subst-id-cod (sym bridge-eo)
            ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk)
    raw-as-view-out = begin
        rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur})
          ≈⟨ ≈-Term-sym idˡ ⟩
        id ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}))
          ≈⟨ ≈-Term-sym cod-cancel ⟩∘⟨refl ⟩
        (BoxAssoc.subst-id-cod (sym bridge-eo) ∘ BoxAssoc.subst-id-cod bridge-eo)
          ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}))
          ≈⟨ FM.assoc ⟩
        BoxAssoc.subst-id-cod (sym bridge-eo)
          ∘ (BoxAssoc.subst-id-cod bridge-eo
             ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur})))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym (view-to-raw-clean eoBlk Pblk rgBlk) ⟩
        BoxAssoc.subst-id-cod (sym bridge-eo) ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk) ∎
      where
        cod-cancel :
          BoxAssoc.subst-id-cod (sym bridge-eo) ∘ BoxAssoc.subst-id-cod bridge-eo ≈Term id
        cod-cancel = lemma bridge-eo
          where
            lemma : ∀ {a b : List X} (e : a ≡ b)
              → BoxAssoc.subst-id-cod (sym e) ∘ BoxAssoc.subst-id-cod e ≈Term id
            lemma refl = idˡ

    -- the HEAD collapse: σ-out's leading `rTo eL (pL++rL) ∘ (id⊗rTo pL rL) ∘ α⇒`
    -- telescopes (via `cit-assoc-head` + α⇐∘α⇒≈id + `raw-as-view-out`) to the
    -- output view `to(view≅ eoBlk Pblk rgBlk)`, framed by subst bridges.
    head-frame :
      rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur}
      ≈Term (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
             ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk)
    head-frame = begin
        rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur}
          ≈⟨ FM.sym-assoc ⟩
        (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL)) ∘ α⇒ {Ue} {Up} {Ur}
          -- re-express the right-nested head via `cit-assoc-head` (peel subst).
          ≈⟨ ≈-Term-sym tail-eq ⟩∘⟨refl ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur}))
          ∘ α⇒ {Ue} {Up} {Ur}
          ≈⟨ FM.assoc ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ ((rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur})
             ∘ α⇒ {Ue} {Up} {Ur})
          -- regroup so `(rTo eL pL ⊗ id) ∘ (α⇐ ∘ α⇒)` is adjacent.
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (rTo (eL ++ pL) rL
             ∘ (((rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur}) ∘ α⇒ {Ue} {Up} {Ur}))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (rTo (eL ++ pL) rL
             ∘ ((rTo eL pL ⊗₁ id {Ur}) ∘ (α⇐ {Ue} {Up} {Ur} ∘ α⇒ {Ue} {Up} {Ur})))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇐∘α⇒≈id ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (rTo (eL ++ pL) rL ∘ ((rTo eL pL ⊗₁ id {Ur}) ∘ id))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idʳ ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}))
          ≈⟨ refl⟩∘⟨ raw-as-view-out ⟩
        BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ (BoxAssoc.subst-id-cod (sym bridge-eo) ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk))
          ≈⟨ FM.sym-assoc ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk) ∎
      where
        -- `subst-id-dom(sym ++-assoc) ∘ (rTo(eL++pL)rL ∘ (rTo eL pL ⊗ id) ∘ α⇐)
        --    ≈ rTo eL (pL++rL) ∘ (id ⊗ rTo pL rL)` (cancel the subst via cit-assoc-head).
        tail-eq :
          BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
            ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur})
          ≈Term rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL)
        tail-eq = begin
            BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ (rTo (eL ++ pL) rL ∘ (rTo eL pL ⊗₁ id {Ur}) ∘ α⇐ {Ue} {Up} {Ur})
              ≈⟨ refl⟩∘⟨ cit-assoc-head ⟩
            BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ (BoxAssoc.subst-id-dom (++-assoc eL pL rL)
                 ∘ (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL)))
              ≈⟨ FM.sym-assoc ⟩
            (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-dom (++-assoc eL pL rL))
              ∘ (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL))
              ≈⟨ dom-cancel ⟩∘⟨refl ⟩
            id ∘ (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL))
              ≈⟨ idˡ ⟩
            rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL) ∎
          where
            dom-cancel :
              BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
                ∘ BoxAssoc.subst-id-dom (++-assoc eL pL rL)
              ≈Term id
            dom-cancel = lemma (++-assoc eL pL rL)
              where
                lemma : ∀ {a b : List X} (e : a ≡ b)
                  → BoxAssoc.subst-id-dom (sym e) ∘ BoxAssoc.subst-id-dom e ≈Term id
                lemma refl = idˡ

    -- the combined `map-++` codomain bridge of `view-to-raw-clean Pblk eoBlk rgBlk`.
    bridge-Po : (pL ++ eL) ++ rL ≡ map C.vlab ((Pblk ++ eoBlk) ++ rgBlk)
    bridge-Po = trans (cong (_++ rL) (sym (map-++ C.vlab Pblk eoBlk)))
                      (sym (map-++ C.vlab (Pblk ++ eoBlk) rgBlk))

    -- `c-iso-assoc-to pL eL rL`, trailing subst reassociated to the right.
    cit-assoc-tail :
      rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur}) ∘ α⇐ {Up} {Ue} {Ur}
      ≈Term BoxAssoc.subst-id-dom (++-assoc pL eL rL)
            ∘ (rTo pL (eL ++ rL) ∘ (id {Up} ⊗₁ rTo eL rL))
    cit-assoc-tail = begin
        rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur}) ∘ α⇐ {Up} {Ue} {Ur}
          ≈⟨ BoxAssoc.c-iso-assoc-to pL eL rL ⟩
        BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ (rTo pL (eL ++ rL) ∘ (id {Up} ⊗₁ rTo eL rL)) ∎

    -- the TAIL collapse (dual of `Sin.out-frame`): `to(view≅ Pblk eoBlk rgBlk)`
    -- post-composed with σ-out's tail `α⇐{Up}{Ue}{Ur} ∘ (id{Up}⊗rFrom eL rL)`
    -- telescopes to the single-block `rTo pL (eL++rL)` (= raw `to(uf++ Pblk
    -- (eoBlk++rgBlk))`), framed by subst bridges.
    tail-frame :
      _≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk)
        ∘ α⇐ {Up} {Ue} {Ur}
        ∘ (id {Up} ⊗₁ rFrom eL rL)
      ≈Term BoxAssoc.subst-id-cod bridge-Po
            ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
            ∘ rTo pL (eL ++ rL)
    tail-frame = begin
        _≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk)
          ∘ α⇐ {Up} {Ue} {Ur}
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ≈⟨ view-to-raw-clean Pblk eoBlk rgBlk ⟩∘⟨refl ⟩
        (BoxAssoc.subst-id-cod bridge-Po
          ∘ (rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur})))
          ∘ α⇐ {Up} {Ue} {Ur}
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          -- peel scod out; bring the raw `to`-block adjacent to `α⇐` then `(id⊗rFrom)`.
          ≈⟨ FM.assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ (rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur}))
          ∘ α⇐ {Up} {Ue} {Ur}
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ rTo (pL ++ eL) rL
          ∘ ((rTo pL eL ⊗₁ id {Ur})
             ∘ α⇐ {Up} {Ue} {Ur}
             ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- group `rTo(pL++eL)rL ∘ (rTo pL eL ⊗ id) ∘ α⇐` for `cit-assoc-tail`.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ rTo (pL ++ eL) rL
          ∘ (((rTo pL eL ⊗₁ id {Ur}) ∘ α⇐ {Up} {Ue} {Ur})
             ∘ (id {Up} ⊗₁ rFrom eL rL))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ (rTo (pL ++ eL) rL
             ∘ ((rTo pL eL ⊗₁ id {Ur}) ∘ α⇐ {Up} {Ue} {Ur}))
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ ((rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur})) ∘ α⇐ {Up} {Ue} {Ur})
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ (rTo (pL ++ eL) rL ∘ (rTo pL eL ⊗₁ id {Ur}) ∘ α⇐ {Up} {Ue} {Ur})
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          -- apply `cit-assoc-tail` to the left-nested `to`-block + α⇐.
          ≈⟨ refl⟩∘⟨ cit-assoc-tail ⟩∘⟨refl ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ (BoxAssoc.subst-id-dom (++-assoc pL eL rL)
             ∘ (rTo pL (eL ++ rL) ∘ (id {Up} ⊗₁ rTo eL rL)))
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          -- collapse `(id{Up}⊗rTo eL rL) ∘ (id{Up}⊗rFrom eL rL) = id`.
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ (rTo pL (eL ++ rL) ∘ (id {Up} ⊗₁ rTo eL rL))
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ rTo pL (eL ++ rL)
          ∘ ((id {Up} ⊗₁ rTo eL rL) ∘ (id {Up} ⊗₁ rFrom eL rL))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ rTo pL (eL ++ rL)
          ∘ ((id {Up} ∘ id {Up}) ⊗₁ (rTo eL rL ∘ rFrom eL rL))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ eL rL)) ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ rTo pL (eL ++ rL)
          ∘ (id {Up} ⊗₁ id {unflatten (eL ++ rL)})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ id⊗id≈id ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ rTo pL (eL ++ rL)
          ∘ id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idʳ ⟩
        BoxAssoc.subst-id-cod bridge-Po
          ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ∘ rTo pL (eL ++ rL) ∎

    -- the assembled raw composite: σ-out chained through head-frame,
    -- σ-frame-app-to′, tail-frame (dual of `Sin.sin-assembled`).
    sout-assembled :
      σ-out-raw
      ≈Term (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
             ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
            ∘ (BoxAssoc.subst-id-cod bridge-Po
               ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
               ∘ rTo pL (eL ++ rL))
    sout-assembled = begin
        σ-out-raw
          -- regroup the right-associated σ-out into HEAD ∘ (σ⊗id) ∘ TAIL.
          ≈⟨ regroup-blocks ⟩
        (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur})
          ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
          ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- (1) head-frame on the leading `rTo ∘ (id⊗rTo) ∘ α⇒`.
          ≈⟨ head-frame ⟩∘⟨refl ⟩
        ((BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
           ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk))
          ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
          ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- regroup so `to(view≅ eoBlk Pblk rgBlk) ∘ (σ⊗id)` is adjacent.
          ≈⟨ regroup-σ ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ (_≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk) ∘ (σ {Up} {Ue} ⊗₁ id {Ur}))
          ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- (2) σ-frame-app-to′.
          ≈⟨ refl⟩∘⟨ BNV.σ-frame-app-to′ C.vlab Pblk eoBlk rgBlk ⟩∘⟨refl ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ (pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
             ∘ _≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk))
          ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- regroup so `to(view≅ Pblk eoBlk rgBlk) ∘ α⇐ ∘ (id⊗rFrom)` is adjacent.
          ≈⟨ regroup-tail ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (_≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk)
             ∘ α⇐ {Up} {Ue} {Ur}
             ∘ (id {Up} ⊗₁ rFrom eL rL))
          -- (3) tail-frame.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ tail-frame ⟩
        (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
          ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (BoxAssoc.subst-id-cod bridge-Po
             ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
             ∘ rTo pL (eL ++ rL)) ∎
      where
        -- σ-out (right-associated) regrouped into HEAD ∘ (σ⊗id) ∘ TAIL.
        regroup-blocks :
          σ-out-raw
          ≈Term (rTo eL (pL ++ rL) ∘ (id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur})
            ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
            ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
        regroup-blocks = begin
            rTo eL (pL ++ rL)
              ∘ (id {Ue} ⊗₁ rTo pL rL)
              ∘ α⇒ {Ue} {Up} {Ur}
              ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
              ∘ α⇐ {Up} {Ue} {Ur}
              ∘ (id {Up} ⊗₁ rFrom eL rL)
              -- shift the split point so HEAD = `rTo ∘ (id⊗rTo) ∘ α⇒`.
              ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            rTo eL (pL ++ rL)
              ∘ ((id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur})
              ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
              ∘ α⇐ {Up} {Ue} {Ur}
              ∘ (id {Up} ⊗₁ rFrom eL rL)
              ≈⟨ FM.sym-assoc ⟩
            (rTo eL (pL ++ rL) ∘ ((id {Ue} ⊗₁ rTo pL rL) ∘ α⇒ {Ue} {Up} {Ur}))
              ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
              ∘ α⇐ {Up} {Ue} {Ur}
              ∘ (id {Up} ⊗₁ rFrom eL rL) ∎

        -- regroup the head substs out and bring `to(view≅) ∘ (σ⊗id)` adjacent.
        regroup-σ :
          ((BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
             ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk))
            ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
            ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          ≈Term (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
                 ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ (_≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk) ∘ (σ {Up} {Ue} ⊗₁ id {Ur}))
            ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
        regroup-σ = begin
            ((BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
               ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
              ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk))
              ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
              ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
              ≈⟨ FM.assoc ⟩
            (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
              ∘ _≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk)
              ∘ (σ {Up} {Ue} ⊗₁ id {Ur})
              ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
              ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
              ∘ (_≅_.to (BNV.view≅ C.vlab eoBlk Pblk rgBlk) ∘ (σ {Up} {Ue} ⊗₁ id {Ur}))
              ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL)) ∎

        -- regroup so `to(view≅ Pblk eoBlk rgBlk) ∘ (α⇐ ∘ (id⊗rFrom))` is one factor,
        -- with `pvlC(app-swap)` peeled to the front.
        regroup-tail :
          (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
            ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ (pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
               ∘ _≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk))
            ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
          ≈Term (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
                 ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
            ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
            ∘ (_≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk)
               ∘ α⇐ {Up} {Ue} {Ur}
               ∘ (id {Up} ⊗₁ rFrom eL rL))
        regroup-tail = begin
            (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
              ∘ (pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
                 ∘ _≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk))
              ∘ (α⇐ {Up} {Ue} {Ur} ∘ (id {Up} ⊗₁ rFrom eL rL))
              -- associate the `(pvlC ∘ to(view≅)) ∘ (α⇐ ∘ (id⊗rFrom))` block.
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
              ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
              ∘ (_≅_.to (BNV.view≅ C.vlab Pblk eoBlk rgBlk)
                 ∘ α⇐ {Up} {Ue} {Ur}
                 ∘ (id {Up} ⊗₁ rFrom eL rL)) ∎

    ----------------------------------------------------------------------
    -- ### Boundary reconciliation: the assembled raw composite vs the
    -- pristine `pvlC(shifts) ∘ to(uf++)` form.  Pure subst-id bookkeeping
    -- (vertical mirror of `Sin`'s boundary).

    -- codomain reframe (σ-out's raw cod `unflatten(eL++(pL++rL))` → `map`-image cod).
    dom-list : eL ++ (pL ++ rL) ≡ map C.vlab (eoBlk ++ (Pblk ++ rgBlk))
    dom-list = trans (cong (eL ++_) (sym (map-++ C.vlab Pblk rgBlk)))
                     (sym (map-++ C.vlab eoBlk (Pblk ++ rgBlk)))

    -- domain reframe (σ-out's raw dom `Up ⊗ unflatten(eL++rL)` → tensor over
    -- the combined `map(eoBlk++rgBlk)`).
    cod-list : eL ++ rL ≡ map C.vlab (eoBlk ++ rgBlk)
    cod-list = sym (map-++ C.vlab eoBlk rgBlk)

    -- tensor-domain subst-id morphism `Up ⊗ unflatten d → Up ⊗ unflatten c`
    -- (precompose; dual of `Sin.tcod`).
    tdom : ∀ {c d : List X} → c ≡ d → HomTerm (Up ⊗₀ unflatten d) (Up ⊗₀ unflatten c)
    tdom {c} e = subst (λ z → HomTerm (Up ⊗₀ unflatten z) (Up ⊗₀ unflatten c)) e id

    -- combined codomain bridge for `to(uf++ Pblk (eoBlk++rgBlk))`'s raw form.
    cod-uf : pL ++ (eL ++ rL) ≡ map C.vlab (Pblk ++ (eoBlk ++ rgBlk))
    cod-uf = trans (cong (pL ++_) cod-list)
                   (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk)))

    -- the raw single-block `rawTo₀ pL (map(eo++rg))` expressed via the raw
    -- `rawTo₀ pL (eL++rL)`, conjugated by the `map-++ eoBlk rgBlk` split
    -- (`tdom` on the domain, `subst-id-cod` on the inner codomain).  Dual of
    -- `Sin.split-gen`; `J` on `cod-list`.
    split-gen-to :
      ∀ {W : List X} (e : eL ++ rL ≡ W)
      → rTo pL W
        ≈Term BoxAssoc.subst-id-cod (cong (pL ++_) e) ∘ rTo pL (eL ++ rL) ∘ tdom e
    split-gen-to refl = ≈-Term-sym (≈-Term-trans idˡ idʳ)

    split-eq-to :
      rTo pL (map C.vlab (eoBlk ++ rgBlk))
      ≈Term BoxAssoc.subst-id-cod (cong (pL ++_) cod-list)
            ∘ rTo pL (eL ++ rL) ∘ tdom cod-list
    split-eq-to = split-gen-to cod-list

    -- two subst-id-cods compose (re-stated locally for the `to`-side merge).
    sidcod-∘ : ∀ {a b c : List X} (p : a ≡ b) (q : b ≡ c)
             → BoxAssoc.subst-id-cod q ∘ BoxAssoc.subst-id-cod p
               ≈Term BoxAssoc.subst-id-cod (trans p q)
    sidcod-∘ refl refl = idˡ

    -- the BTC.uf++ output iso `to`, in raw subst-conjugated form (dual of
    -- `Sin.from-uf-raw`).
    to-uf-raw : _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk))
              ≈Term BoxAssoc.subst-id-cod cod-uf
                    ∘ rTo pL (eL ++ rL)
                    ∘ tdom cod-list
    to-uf-raw = begin
        _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk))
          ≈⟨ ≡⇒≈Term (to-BTC Pblk (eoBlk ++ rgBlk)) ⟩
        subst₂ HomTerm refl (cong unflatten (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk))))
          (rTo pL (map C.vlab (eoBlk ++ rgBlk)))
          ≈⟨ subst-cod-conj (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk)))
               (rTo pL (map C.vlab (eoBlk ++ rgBlk))) ⟩
        BoxAssoc.subst-id-cod (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk)))
          ∘ rTo pL (map C.vlab (eoBlk ++ rgBlk))
          ≈⟨ refl⟩∘⟨ split-eq-to ⟩
        BoxAssoc.subst-id-cod (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk)))
          ∘ (BoxAssoc.subst-id-cod (cong (pL ++_) cod-list)
             ∘ rTo pL (eL ++ rL) ∘ tdom cod-list)
          ≈⟨ FM.sym-assoc ⟩
        (BoxAssoc.subst-id-cod (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk)))
          ∘ BoxAssoc.subst-id-cod (cong (pL ++_) cod-list))
          ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
          ≈⟨ sidcod-∘ (cong (pL ++_) cod-list)
                      (sym (map-++ C.vlab Pblk (eoBlk ++ rgBlk))) ⟩∘⟨refl ⟩
        BoxAssoc.subst-id-cod cod-uf ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
          ≈⟨ ≈-Term-refl ⟩
        BoxAssoc.subst-id-cod cod-uf ∘ rTo pL (eL ++ rL) ∘ tdom cod-list ∎

    ----------------------------------------------------------------------
    -- ### tensor-dom reframe helpers (the shared `sidX` machinery lives in
    -- `BlockFactor` scope; see `sidX`, `scod→sidX`, … above).

    tdom₂ : ∀ {c d : List X} (q : c ≡ d)
          → tdom q ≡ subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten q)) refl
                            (id {Up ⊗₀ unflatten c})
    tdom₂ refl = refl

    -- conjugation of σ-out-raw by the dom/cod reframes (dom over `Up ⊗ unflatten`).
    subst₂-conj-tensor-dom :
      ∀ {a b : List X} {c d : List X} (p : a ≡ b) (q : c ≡ d)
        (t : HomTerm (Up ⊗₀ unflatten c) (unflatten a))
      → subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten q)) (cong unflatten p) t
        ≈Term BoxAssoc.subst-id-cod p ∘ t ∘ tdom q
    subst₂-conj-tensor-dom refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)

    ----------------------------------------------------------------------
    -- ### The two boundary equalities (subst-id-morphism uniqueness).

    -- LEFT of `pvlC(app-swap)` (codomain side): the assembled output substs vs
    -- `shifts`' first bridge `sidC(++-assoc eoBlk Pblk rgBlk)`.
    left-eq :
      BoxAssoc.subst-id-cod dom-list
        ∘ (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
           ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
      ≈Term sidC (++-assoc eoBlk Pblk rgBlk)
    left-eq = begin
        BoxAssoc.subst-id-cod dom-list
          ∘ (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
             ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
          ≈⟨ scod→sidX dom-list
             ⟩∘⟨ (sdd→sidX (sym (++-assoc eL pL rL)) ⟩∘⟨ scod→sidX (sym bridge-eo)) ⟩
        sidX dom-list
          ∘ (sidX (sym (sym (++-assoc eL pL rL))) ∘ sidX (sym bridge-eo))
          ≈⟨ refl⟩∘⟨ sidX-∘ (sym bridge-eo) (sym (sym (++-assoc eL pL rL))) ⟩
        sidX dom-list
          ∘ sidX (trans (sym bridge-eo) (sym (sym (++-assoc eL pL rL))))
          ≈⟨ sidX-∘ (trans (sym bridge-eo) (sym (sym (++-assoc eL pL rL)))) dom-list ⟩
        sidX (trans (trans (sym bridge-eo) (sym (sym (++-assoc eL pL rL)))) dom-list)
          ≈⟨ sidX-irrel _ (cong (map C.vlab) (++-assoc eoBlk Pblk rgBlk)) ⟩
        sidX (cong (map C.vlab) (++-assoc eoBlk Pblk rgBlk))
          ≈⟨ ≈-Term-sym (sidC→sidX (++-assoc eoBlk Pblk rgBlk)) ⟩
        sidC (++-assoc eoBlk Pblk rgBlk) ∎

    -- RIGHT of `pvlC(app-swap)` (domain side): the assembled output substs vs
    -- `shifts`' second bridge `sidC(sym(++-assoc Pblk eoBlk rgBlk))`, modulo
    -- the shared `rTo`.
    right-eq :
      BoxAssoc.subst-id-cod bridge-Po ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
      ≈Term sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ BoxAssoc.subst-id-cod cod-uf
    right-eq = begin
        BoxAssoc.subst-id-cod bridge-Po ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
          ≈⟨ scod→sidX bridge-Po ⟩∘⟨ sdd→sidX (++-assoc pL eL rL) ⟩
        sidX bridge-Po ∘ sidX (sym (++-assoc pL eL rL))
          ≈⟨ sidX-∘ (sym (++-assoc pL eL rL)) bridge-Po ⟩
        sidX (trans (sym (++-assoc pL eL rL)) bridge-Po)
          ≈⟨ sidX-irrel _ (trans cod-uf (cong (map C.vlab) (sym (++-assoc Pblk eoBlk rgBlk)))) ⟩
        sidX (trans cod-uf (cong (map C.vlab) (sym (++-assoc Pblk eoBlk rgBlk))))
          ≈⟨ ≈-Term-sym (sidX-∘ cod-uf (cong (map C.vlab) (sym (++-assoc Pblk eoBlk rgBlk)))) ⟩
        sidX (cong (map C.vlab) (sym (++-assoc Pblk eoBlk rgBlk))) ∘ sidX cod-uf
          ≈⟨ ≈-Term-sym (sidC→sidX (sym (++-assoc Pblk eoBlk rgBlk)))
             ⟩∘⟨ ≈-Term-sym (scod→sidX cod-uf) ⟩
        sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ BoxAssoc.subst-id-cod cod-uf ∎

    ----------------------------------------------------------------------
    -- ### The final lemma: box-braid's output braid `σ-out` (reframed onto the
    -- `map C.vlab (·)` endpoints) is the `pvlC` of `shifts` post-composed onto
    -- the `BTC.uf++` output iso `to`.
    σout-as-pvl :
      subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten cod-list))
                     (cong unflatten dom-list) σ-out-raw
      ≈Term pvlC (PermProp.shifts Pblk eoBlk {rgBlk})
            ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk))
    σout-as-pvl = begin
        subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten cod-list))
                       (cong unflatten dom-list) σ-out-raw
          ≈⟨ subst₂-conj-tensor-dom dom-list cod-list σ-out-raw ⟩
        BoxAssoc.subst-id-cod dom-list ∘ σ-out-raw ∘ tdom cod-list
          ≈⟨ refl⟩∘⟨ sout-assembled ⟩∘⟨refl ⟩
        BoxAssoc.subst-id-cod dom-list
          ∘ ((BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
              ∘ BoxAssoc.subst-id-cod (sym bridge-eo))
             ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
             ∘ (BoxAssoc.subst-id-cod bridge-Po
                ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL)
                ∘ rTo pL (eL ++ rL)))
          ∘ tdom cod-list
          -- regroup: cluster the LEFT substs onto `scod dom-list`, the RIGHT
          -- substs + `rTo ∘ tdom` onto the output block.
          ≈⟨ regroup ⟩
        (BoxAssoc.subst-id-cod dom-list
          ∘ (BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
             ∘ BoxAssoc.subst-id-cod (sym bridge-eo)))
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (BoxAssoc.subst-id-cod bridge-Po
             ∘ BoxAssoc.subst-id-dom (++-assoc pL eL rL))
          ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
          -- (LEFT) left-eq; (RIGHT) right-eq.
          ≈⟨ left-eq ⟩∘⟨ (refl⟩∘⟨ (right-eq ⟩∘⟨refl)) ⟩
        sidC (++-assoc eoBlk Pblk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ BoxAssoc.subst-id-cod cod-uf)
          ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
          -- reassemble the trailing block into `sidC(sym ++-assoc) ∘ to(uf++)`.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ reassemble-right ⟩
        sidC (++-assoc eoBlk Pblk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)))
          -- fold `sidC ∘ pvlC(app-swap) ∘ sidC` back into `pvlC(shifts)`.
          ≈⟨ FM.sym-assoc ⟩
        (sidC (++-assoc eoBlk Pblk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk))
          ∘ (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)))
          ≈⟨ FM.sym-assoc ⟩
        ((sidC (++-assoc eoBlk Pblk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk))
          ∘ sidC (sym (++-assoc Pblk eoBlk rgBlk)))
          ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk))
          ≈⟨ ≈-Term-sym shifts-fold ⟩∘⟨refl ⟩
        pvlC (PermProp.shifts Pblk eoBlk {rgBlk})
          ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)) ∎
      where
        -- big associativity regroup (pure ∘-reshuffle).
        sL = BoxAssoc.subst-id-cod dom-list
        L1 = BoxAssoc.subst-id-dom (sym (++-assoc eL pL rL))
        L2 = BoxAssoc.subst-id-cod (sym bridge-eo)
        pA = pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
        R1 = BoxAssoc.subst-id-cod bridge-Po
        R2 = BoxAssoc.subst-id-dom (++-assoc pL eL rL)
        rT = rTo pL (eL ++ rL)
        tD = tdom cod-list

        regroup :
          sL ∘ ((L1 ∘ L2) ∘ pA ∘ (R1 ∘ R2 ∘ rT)) ∘ tD
          ≈Term (sL ∘ (L1 ∘ L2)) ∘ pA ∘ (R1 ∘ R2) ∘ (rT ∘ tD)
        regroup = begin
            sL ∘ ((L1 ∘ L2) ∘ pA ∘ (R1 ∘ R2 ∘ rT)) ∘ tD
              ≈⟨ FM.sym-assoc ⟩
            (sL ∘ ((L1 ∘ L2) ∘ pA ∘ (R1 ∘ R2 ∘ rT))) ∘ tD
              ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
            ((sL ∘ (L1 ∘ L2)) ∘ (pA ∘ (R1 ∘ R2 ∘ rT))) ∘ tD
              ≈⟨ FM.assoc ⟩
            (sL ∘ (L1 ∘ L2)) ∘ (pA ∘ (R1 ∘ R2 ∘ rT)) ∘ tD
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            (sL ∘ (L1 ∘ L2)) ∘ pA ∘ ((R1 ∘ R2 ∘ rT) ∘ tD)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            (sL ∘ (L1 ∘ L2)) ∘ pA ∘ R1 ∘ ((R2 ∘ rT) ∘ tD)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            (sL ∘ (L1 ∘ L2)) ∘ pA ∘ R1 ∘ (R2 ∘ (rT ∘ tD))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            (sL ∘ (L1 ∘ L2)) ∘ pA ∘ (R1 ∘ R2) ∘ (rT ∘ tD) ∎

        -- fold `sidC(++-assoc) ∘ pvlC(app-swap) ∘ sidC(sym ++-assoc)` into `pvlC(shifts)`.
        shifts-fold :
          pvlC (PermProp.shifts Pblk eoBlk {rgBlk})
          ≈Term (sidC (++-assoc eoBlk Pblk rgBlk)
                 ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk))
                ∘ sidC (sym (++-assoc Pblk eoBlk rgBlk))
        shifts-fold = ≈-Term-trans (pvlC-shifts Pblk eoBlk rgBlk) FM.sym-assoc

        reassemble-right :
          (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ BoxAssoc.subst-id-cod cod-uf)
            ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
          ≈Term sidC (sym (++-assoc Pblk eoBlk rgBlk))
                ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk))
        reassemble-right = begin
            (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ BoxAssoc.subst-id-cod cod-uf)
              ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
              ≈⟨ FM.assoc ⟩
            sidC (sym (++-assoc Pblk eoBlk rgBlk))
              ∘ BoxAssoc.subst-id-cod cod-uf ∘ (rTo pL (eL ++ rL) ∘ tdom cod-list)
              ≈⟨ refl⟩∘⟨ ≈-Term-sym to-uf-raw ⟩
            sidC (sym (++-assoc Pblk eoBlk rgBlk))
              ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)) ∎

  ------------------------------------------------------------------------
  -- ### `box-braid-pvl` — Milestone 1.  The σ-mirror `box-braid` with both
  -- block-swap braids `σ-in`/`σ-out` rewritten into the `BTC.uf++`-framed
  -- `pvlC`-of-`shifts` form (via `Sin.σin-as-pvl` / `Sout.σout-as-pvl`).
  --
  -- The FRONT-acting box `box-of eiBlk eoBlk (Pblk++rgBlk) g` (un-split
  -- residual) — reframed (`subst₂` over the two `dom-list` `map-++` bridges)
  -- onto the `map C.vlab (·++(·++·))` endpoints — factors as
  --
  --   (pvlC(shifts Pblk eoBlk) ∘ to(uf++ Pblk (eoBlk++rgBlk)))
  --     ∘ (id {U Pblk} ⊗₁ BoxSub)
  --     ∘ (from(uf++ Pblk (eiBlk++rgBlk)) ∘ pvlC(shifts eiBlk Pblk))
  --
  -- where `BoxSub` is the SAME pure-block box `head-factor-K` uses (the
  -- `map-++ C.vlab`-substituted `box-of` on the block lists `eiBlk`/`eoBlk`/
  -- `rgBlk`).  This is the per-FIRE-edge tool that brings the actual mixed
  -- FRONT box into `head-factor-K`'s prefix-held input for the K induction.
  --
  -- Proof: `box-braid` (at the `map C.vlab` images) gives the LHS box-of as
  -- `σ-out-raw ∘ (id{Up} ⊗₁ box-of … rgBlk) ∘ σ-in-raw` (definitionally the
  -- `Sin`/`Sout` raw σ-braids); the outer `subst₂` distributes over the
  -- 3-composite (`subst₂-HomTerm-∘-dist`, inserting the two `Up ⊗₀ unflatten
  -- cod-list` intermediate transports) into exactly the `σout-as-pvl` LHS, the
  -- `⊗-push`'d middle (= `id{Up} ⊗₁ BoxSub`), and the `σin-as-pvl` LHS.
  box-braid-pvl
    : ∀ (eiBlk eoBlk Pblk rgBlk : List (Fin C.nV))
        (g : FlatGen (map C.vlab eiBlk) (map C.vlab eoBlk))
    → subst₂ HomTerm
        (cong unflatten (Sin.dom-list eiBlk Pblk rgBlk))
        (cong unflatten (Sout.dom-list eoBlk Pblk rgBlk))
        (box-of (map C.vlab eiBlk) (map C.vlab eoBlk)
                (map C.vlab Pblk ++ map C.vlab rgBlk) g)
      ≈Term
        ( pvlC (PermProp.shifts Pblk eoBlk {rgBlk})
          ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)) )
        ∘ (id {unflatten (map C.vlab Pblk)}
           ⊗₁ subst₂ HomTerm
                (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                (box-of (map C.vlab eiBlk) (map C.vlab eoBlk) (map C.vlab rgBlk) g))
        ∘ ( _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
            ∘ pvlC (PermProp.shifts eiBlk Pblk {rgBlk}) )
  box-braid-pvl eiBlk eoBlk Pblk rgBlk g = ≈-Term-trans (≈-Term-trans braid-subst (≡⇒≈Term split)) reframe
    where
      module Si = Sin eiBlk Pblk rgBlk
      module So = Sout eoBlk Pblk rgBlk

      eiL = map C.vlab eiBlk
      eoL = map C.vlab eoBlk
      pL  = map C.vlab Pblk
      rL  = map C.vlab rgBlk
      Up  = unflatten pL

      g-box-rest = box-of eiL eoL rL g
      g-box-full = box-of eiL eoL (pL ++ rL) g

      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                 g-box-rest

      -- the two intermediate `Up ⊗₀ unflatten (cod-list)` transports.
      qi = cong (Up ⊗₀_) (cong unflatten (Si.cod-list))
      qo = cong (Up ⊗₀_) (cong unflatten (So.cod-list))

      mid0 = id {Up} ⊗₁ g-box-rest

      -- `box-braid` (instantiated at the `map C.vlab` images); its `σ-in`/
      -- `σ-out` ARE `Si.σ-in-raw`/`So.σ-out-raw` definitionally.
      braid
        : g-box-full
          ≈Term So.σ-out-raw ∘ (id {Up} ⊗₁ g-box-rest) ∘ Si.σ-in-raw
      braid = BoxAssoc.box-braid pL eiL eoL rL g

      braid-subst
        : subst₂ HomTerm
            (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list)) g-box-full
          ≈Term subst₂ HomTerm
            (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list))
            (So.σ-out-raw ∘ (id {Up} ⊗₁ g-box-rest) ∘ Si.σ-in-raw)
      braid-subst =
        subst₂-resp-≈Term (cong unflatten (Si.dom-list))
                          (cong unflatten (So.dom-list)) braid

      -- `id{Up} ⊗ subst₂ … box`-push (subst on the SECOND ⊗-factor).
      ⊗-push
        : ∀ {a₁ a₂ b₁ b₂ : List X} (r₁ : a₁ ≡ a₂) (r₂ : b₁ ≡ b₂)
            (f : HomTerm (unflatten a₁) (unflatten b₁))
        → subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten r₁))
                         (cong (Up ⊗₀_) (cong unflatten r₂)) (id {Up} ⊗₁ f)
          ≡ id {Up} ⊗₁ (subst₂ HomTerm (cong unflatten r₁) (cong unflatten r₂) f)
      ⊗-push refl refl f = refl

      mid-≡ : subst₂ HomTerm qi qo mid0 ≡ id {Up} ⊗₁ BoxSub
      mid-≡ = ⊗-push (sym (map-++ C.vlab eiBlk rgBlk))
                     (sym (map-++ C.vlab eoBlk rgBlk)) g-box-rest

      -- distribute the outer `subst₂` over the 3-composite, inserting the two
      -- intermediate `Up ⊗₀ unflatten cod-list` transports.
      split
        : subst₂ HomTerm
            (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list))
            (So.σ-out-raw ∘ (id {Up} ⊗₁ g-box-rest) ∘ Si.σ-in-raw)
          ≡ (subst₂ HomTerm qo (cong unflatten (So.dom-list)) So.σ-out-raw)
            ∘ (id {Up} ⊗₁ BoxSub)
            ∘ (subst₂ HomTerm (cong unflatten (Si.dom-list)) qi Si.σ-in-raw)
      split =
        trans
          (subst₂-HomTerm-∘-dist
             (cong unflatten (Si.dom-list)) qo (cong unflatten (So.dom-list))
             So.σ-out-raw ((id {Up} ⊗₁ g-box-rest) ∘ Si.σ-in-raw))
          (cong (subst₂ HomTerm qo (cong unflatten (So.dom-list)) So.σ-out-raw ∘_)
            (trans
              (subst₂-HomTerm-∘-dist
                 (cong unflatten (Si.dom-list)) qi qo mid0 Si.σ-in-raw)
              (cong (_∘ subst₂ HomTerm (cong unflatten (Si.dom-list)) qi Si.σ-in-raw)
                    mid-≡)))

      reframe
        : (subst₂ HomTerm qo (cong unflatten (So.dom-list)) So.σ-out-raw)
          ∘ (id {Up} ⊗₁ BoxSub)
          ∘ (subst₂ HomTerm (cong unflatten (Si.dom-list)) qi Si.σ-in-raw)
          ≈Term
          ( pvlC (PermProp.shifts Pblk eoBlk {rgBlk})
            ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)) )
          ∘ (id {Up} ⊗₁ BoxSub)
          ∘ ( _≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk))
              ∘ pvlC (PermProp.shifts eiBlk Pblk {rgBlk}) )
      reframe =
        ∘-resp-≈ So.σout-as-pvl
          (∘-resp-≈ ≈-Term-refl Si.σin-as-pvl)

  ------------------------------------------------------------------------
  -- ### Milestone 2b proper: `kblock-factor` — base-case scaffolding.
  --
  -- `kblock-factor` (assembled below) goes through a generalised
  -- perm-tracking induction `kfac-gen es P ys s (pf : s ↭ map injL P ++ map
  -- injR ys) Br res`
  --   : pe-termC (map ψK es) s ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf
  -- (the K-prepend wrinkle forbids a clean stack `≡`, so the actual stack `s`
  -- + a perm-to-clean `pf` are threaded, mirroring `process-edges-↑ʳ-on-perm`;
  -- `kblock-factor` is the `s = clean, pf = ↭-refl, Br = ↭-sym KBraid` instance).
  -- The two base-case pieces below — `KClean-nil` (the `es = []` clean target
  -- collapses to `id`) and `pvlC-cancel` (the round-trip `pvlC Br ∘ pvlC pf`
  -- collapses to `id` on a `Unique` stack via the keystone) — discharge the
  -- `es = []` case.
  --
  -- The CLEAN-side `Kterm`/`KClean` cons telescoping
  -- (`Kterm-cons`/`KClean-cons`, just above the `Linear⇒cod-Unique` block) is:
  --
  --   KClean (e∷es) P ys ≈Term KClean es P (ys-step e ys) ∘ KCleanHead e P ys
  --
  -- where `KCleanHead e P ys = to(uf++) ∘ (id {prefix} ⊗₁ Khead-emb e ys) ∘
  -- from(uf++)` is the clean pure-R single-edge head block.  This reduces the
  -- cons step of `kfac-gen` (after identifying `Br ≈ Br1` via the keystone on
  -- the common Unique codomain `pe-stackC (map ψK es) s1` and cancelling the
  -- shared `pvlC Br1 ∘ KClean es P (ys-step e ys)` tail) to the single
  -- per-edge HEAD reconciliation
  --
  --   kfac-head : pvlC pf1 ∘ tH ≈Term KCleanHead e P ys ∘ pvlC pf
  --
  -- (SKIP: both `tH`/`Khead-emb` are `id`, `KCleanHead ≈ id`, `pf1 ≈ pf` by
  -- keystone.  FIRE: the actual FRONT box `fire-mid C (ψK e) rest ∘ pvlC perm`
  -- on `s` is moved past the `map injL P` prefix by `box-braid-pvl`
  -- (front→prefix) into `head-factor-K`'s prefix-held input, with the four
  -- perms `pf`/`pf1`/`perm`/`permR` reconciled by the keystone `pvlC-coh` on
  -- the Unique codomains and the box framings aligned via `objUIP`).
  --
  -- `KClean [] P ys` collapses to the identity (`Kterm [] ys = id`).
  KClean-nil
    : ∀ (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → KClean [] P ys ≈Term id {unflatten (map C.vlab (map injL P ++ map injR ys))}
  KClean-nil P ys = begin
      _≅_.to (BTC.uf++ (map injL P) (map injR ys))
        ∘ (id {RpreObj P} ⊗₁ Kterm [] ys)
        ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl ≈-Term-refl ⟩∘⟨refl ⟩
      _≅_.to (BTC.uf++ (map injL P) (map injR ys))
        ∘ (id {RpreObj P} ⊗₁ id {RsufObj ys})
        ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))
        ≈⟨ ≈-Term-sym (id-as-tensor (map injL P) (map injR ys)) ⟩
      id ∎

  -- `pvlC Br ∘ pvlC pf ≈ id` when both compose round-trip on a `Unique` list.
  -- (`pvlC` is a ↭-functor for `↭-trans`; the keystone reconciles the
  -- round-trip `s ↭ s` to `↭-refl`.)
  pvlC-cancel
    : ∀ {s c : List (Fin C.nV)} → Unique s
    → (pf : s Perm.↭ c) (Br : c Perm.↭ s)
    → pvlC Br ∘ pvlC pf ≈Term id {unflatten (map C.vlab s)}
  pvlC-cancel uniq pf Br =
    ≈-Term-trans (≈-Term-sym (pvlC-↭trans pf Br))
      (pvlC-coh uniq (Perm.↭-trans pf Br) Perm.↭-refl)

  ------------------------------------------------------------------------
  -- ### `kfac-gen` — the generalised K-side perm-tracking induction.
  --
  -- Mirror of `gblock-factor`, but tracking the K-prepend wrinkle: the
  -- running stack `s` only `↭`s (via `pf`) the clean `map injL P ++ map injR
  -- ys` form, and the post-run codomain `↭`s (via `Br`) the clean target.
  --
  --   pe-termC (map ψK es) s ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf
  --
  -- `Reservoir≤1` (the SOUND freshness side-condition) supplies the
  -- per-edge keystone `Unique` of the running stack.

  -- ABBREVIATIONS shared by the helpers and `kfac-gen` itself.

  -- The K-side edge-step on the pure-K stack (the "clean" stack tracker).
  ys-step : (e : Fin K.nE) (ys : List (Fin K.nV)) → List (Fin K.nV)
  ys-step e ys = proj₁ (edge-step K ys e)

  -- The clean pure-R head: `edge-step C (map injR ys) (ψK e)`.
  zs1 : (e : Fin K.nE) (ys : List (Fin K.nV)) → List (Fin C.nV)
  zs1 e ys = proj₁ (edge-step C-hg (map injR ys) (ψK e))

  kHead : (e : Fin K.nE) (ys : List (Fin K.nV))
        → HomTerm (unflatten (map C.vlab (map injR ys)))
                  (unflatten (map C.vlab (zs1 e ys)))
  kHead e ys = proj₂ (edge-step C-hg (map injR ys) (ψK e))

  -- Pure-R head stack agreement: the clean head stack IS `map injR (ys-step)`.
  zs1-emb
    : (e : Fin K.nE) (ys : List (Fin K.nV))
    → zs1 e ys ≡ map injR (ys-step e ys)
  zs1-emb e ys = TK.edge-step-stack-emb e ys

  -- The CLEAN K-side single-edge head, codomain-transported to `map injR
  -- (ys-step e ys)`: the pure-R analogue of `head-factor`'s `tHL`.
  Khead-emb
    : (e : Fin K.nE) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injR ys)))
              (unflatten (map C.vlab (map injR (ys-step e ys))))
  Khead-emb e ys = coeC {map injR ys} (zs1-emb e ys) (kHead e ys)

  -- `Kterm` cons telescoping: the pure-R run's head ∘ tail IS `Kterm (e∷es)`.
  -- (Mirror of `Lterm-cons`; the pure-R run stays in `map injR _` form so
  -- the stack agreements are genuine `≡`s — NO braid here.)  Generalise the
  -- head stack `zs1ᵍ`/term `kHᵍ`/stack-emb `wEqK` so `zEqᵍ` matches at refl.
  Kterm-cons
    : ∀ (e : Fin K.nE) (es : List (Fin K.nE)) (ys : List (Fin K.nV))
        (zs1ᵍ : List (Fin C.nV))
        (kHᵍ : HomTerm (unflatten (map C.vlab (map injR ys)))
                       (unflatten (map C.vlab zs1ᵍ)))
        (zEqᵍ : zs1ᵍ ≡ map injR (ys-step e ys))
        (wEqK : pe-stackC (map ψK es) zs1ᵍ
                ≡ map injR (pe-stackK (e ∷ es) ys))
    → Kterm es (ys-step e ys) ∘ coeC {map injR ys} zEqᵍ kHᵍ
      ≈Term coeC {map injR ys} wEqK (pe-termC (map ψK es) zs1ᵍ ∘ kHᵍ)
  Kterm-cons e es ys .(map injR (ys-step e ys)) kHᵍ refl wEqK =
    ≡⇒≈Term
      (trans (sym (coeC-∘ (proc-stack-emb-R es (ys-step e ys))
                (pe-termC (map ψK es) (map injR (ys-step e ys))) kHᵍ))
      (cong (λ z → coeC {map injR ys} z
               (pe-termC (map ψK es) (map injR (ys-step e ys)) ∘ kHᵍ))
            (uipL (proc-stack-emb-R es (ys-step e ys)) wEqK)))

  -- The CLEAN single-K-edge block (the pure-R `(id ⊗₁ Khead-emb)` framed by
  -- `BTC.uf++`) — the K-side analogue of `head-factor`'s RHS block.
  KCleanHead
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → HomTerm (unflatten (map C.vlab (map injL P ++ map injR ys)))
              (unflatten (map C.vlab (map injL P ++ map injR (ys-step e ys))))
  KCleanHead e P ys =
    _≅_.to (BTC.uf++ (map injL P) (map injR (ys-step e ys)))
    ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys)
    ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))

  -- `KClean` cons telescoping: the clean run `KClean (e∷es)` factors as the
  -- clean tail `KClean es P (ys-step e ys)` post-composed with the clean head
  -- block `KCleanHead e P ys`.  Mirror of `gblock-factor`'s `cancel-merge`
  -- (LEFT/RIGHT swapped: prefix `map injL P` held by `id`, K-block on `injR`).
  KClean-cons
    : (e : Fin K.nE) (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → KClean (e ∷ es) P ys
      ≈Term KClean es P (ys-step e ys) ∘ KCleanHead e P ys
  KClean-cons e es P ys = begin
      KClean (e ∷ es) P ys
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl Kterm-fac ⟩∘⟨refl ⟩
      to-cod
        ∘ (id {RpreObj P} ⊗₁ (Kterm es (ys-step e ys) ∘ Khead-emb e ys))
        ∘ from-dom
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩∘⟨refl ⟩
      to-cod
        ∘ ((id {RpreObj P} ∘ id {RpreObj P})
           ⊗₁ (Kterm es (ys-step e ys) ∘ Khead-emb e ys))
        ∘ from-dom
        ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
      to-cod
        ∘ ((id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
           ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys))
        ∘ from-dom
        ≈⟨ insert-mid ⟩
      (to-cod
        ∘ (id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
        ∘ from-mid)
        ∘ (to-mid
           ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys)
           ∘ from-dom) ∎
    where
      to-cod  = _≅_.to   (BTC.uf++ (map injL P) (map injR (pe-stackK (e ∷ es) ys)))
      from-dom = _≅_.from (BTC.uf++ (map injL P) (map injR ys))
      to-mid  = _≅_.to   (BTC.uf++ (map injL P) (map injR (ys-step e ys)))
      from-mid = _≅_.from (BTC.uf++ (map injL P) (map injR (ys-step e ys)))

      -- `Kterm (e∷es) ys ≈ Kterm es (ys-step) ∘ Khead-emb`, via `Kterm-cons`
      -- at the REAL head stack `zs1 e ys`/term `kHead e ys`, matched at refl.
      Kterm-fac
        : Kterm (e ∷ es) ys
          ≈Term Kterm es (ys-step e ys) ∘ Khead-emb e ys
      Kterm-fac =
        ≈-Term-sym
          (≈-Term-trans
            (Kterm-cons e es ys (zs1 e ys) (kHead e ys) (zs1-emb e ys)
              (proc-stack-emb-R (e ∷ es) ys))
            (≡⇒≈Term refl))

      -- Insert the middle `from-mid ∘ to-mid = id` between the two ⊗-blocks
      -- and regroup into the two `KClean`/`KCleanHead` composites.
      insert-mid
        : to-cod
          ∘ ((id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
             ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys))
          ∘ from-dom
          ≈Term (to-cod
                  ∘ (id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
                  ∘ from-mid)
                ∘ (to-mid
                   ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys)
                   ∘ from-dom)
      insert-mid = begin
        to-cod
          ∘ ((id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
             ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys))
          ∘ from-dom
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-cod
          ∘ (id {RpreObj P} ⊗₁ Kterm es (ys-step e ys))
          ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys)
          ∘ from-dom
          -- reverse of `cancel-mid-iso`: re-insert the middle `from-mid ∘ to-mid`.
          ≈⟨ ≈-Term-sym
               (cancel-mid-iso to-cod
                  (id {RpreObj P} ⊗₁ Kterm es (ys-step e ys)) from-mid
                  to-mid (id {RpreObj P} ⊗₁ Khead-emb e ys) from-dom
                  (_≅_.isoʳ (BTC.uf++ (map injL P) (map injR (ys-step e ys))))) ⟩
        (to-cod
          ∘ (id {RpreObj P} ⊗₁ Kterm es (ys-step e ys)) ∘ from-mid)
          ∘ to-mid
          ∘ (id {RpreObj P} ⊗₁ Khead-emb e ys)
          ∘ from-dom ∎

  ------------------------------------------------------------------------
  -- ### `kfac-head` — the single-K-edge HEAD reconciliation (K-analogue of
  -- `fire-core`/`edge-suffix-factor`).
  --
  --   pvlC pf1 ∘ tH ≈Term KCleanHead e P ys ∘ pvlC pf
  --
  -- where `tH = proj₂ (edge-step C (ψK e) s)`, `pf : s ↭ injL P ++ injR ys`
  -- (the actual mixed stack only `↭`s the clean form — the K-prepend
  -- wrinkle), and `pf1 : (proj₁ (edge-step C (ψK e) s)) ↭ injL P ++ injR
  -- (ys-step e ys)` (the post-edge actual stack `↭`s the clean post-step).
  --
  -- Dispatched over THREE `EdgeStepR` relation witnesses (mirror of
  -- `edge-suffix-factor`): the pure-K edge `EdgeStepR K ys e` (drives SKIP/
  -- FIRE), the C-actual head `EdgeStepR C s (ψK e)` (= `tH`'s graph), and the
  -- C-pure-R head `EdgeStepR C (map injR ys) (ψK e)` (governs `KCleanHead` via
  -- `kHead`).  The four cross-cases are ruled out by the K↔C extract-prefix
  -- liftings (`extract-prefix-↑ʳ-on-mixed-{just,nothing}` + the `↭`-residual/
  -- nothing transports over `pf`, plus the pure-R injectivity liftings).

  -- C.ein (ψK e) reduces to `map injR (K.ein e)` (the `ein-c-inj₂` bridge).
  ψK-ein : (e : Fin K.nE) → C.ein (ψK e) ≡ map injR (K.ein e)
  ψK-ein e = ein-c-inj₂-red e

  -- Routing: K fires ⇒ C-actual head fires (residual ↭ injL P ++ injR rest).
  clean-just
    : ∀ (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
        (s : List (Fin C.nV)) (rest : List (Fin K.nV))
        (pK : ys Perm.↭ K.ein e ++ rest)
    → s Perm.↭ map injL P ++ map injR ys
    → extract-prefix (K.ein e) ys ≡ just (rest , pK)
    → ∃[ r ] ∃[ q ] extract-prefix (C.ein (ψK e)) s ≡ just (r , q)
                  × (map injL P ++ map injR rest) Perm.↭ r
  clean-just e P ys s rest pK pf eqK =
    let lifted = extract-prefix-↑ʳ-on-mixed-just G.nV (K.ein e) P ys rest pK eqK
        -- the lifted residual perm, on the std stack, retyped via ψK-ein.
        std↭ : map injL P ++ map injR ys
                 Perm.↭ C.ein (ψK e) ++ (map injL P ++ map injR rest)
        std↭ = subst (λ ks → map injL P ++ map injR ys
                               Perm.↭ ks ++ (map injL P ++ map injR rest))
                     (sym (ψK-ein e)) (proj₁ lifted)
        res    = extract-prefix-↭-residual (C.ein (ψK e)) s
                   (map injL P ++ map injR rest)
                   (Perm.↭-trans pf std↭)
    in proj₁ res , proj₁ (proj₂ res) , proj₁ (proj₂ (proj₂ res))
       , proj₂ (proj₂ (proj₂ res))

  -- Routing: K skips ⇒ C-actual head skips.
  clean-nothing
    : ∀ (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
        (s : List (Fin C.nV))
    → s Perm.↭ map injL P ++ map injR ys
    → extract-prefix (K.ein e) ys ≡ nothing
    → extract-prefix (C.ein (ψK e)) s ≡ nothing
  clean-nothing e P ys s pf eqK =
    extract-prefix-↭-nothing (C.ein (ψK e)) (map injL P ++ map injR ys) s
      (Perm.↭-sym pf)
      (subst (λ ks → extract-prefix ks (map injL P ++ map injR ys) ≡ nothing)
             (sym (ψK-ein e))
             (extract-prefix-↑ʳ-on-mixed-nothing G.nV (K.ein e) P ys eqK))

  -- A GENERALISED clean head block, abstracting the K-step stack `ysK` and the
  -- pure-R head term `kh : U(injR ys) → U(injR ysK)`.  `KCleanHead e P ys` is
  -- the instance at `ysK = ys-step e ys`, `kh = Khead-emb e ys`.
  KCleanHead-gen
    : (P : List (Fin G.nV)) (ys ysK : List (Fin K.nV))
      (kh : HomTerm (unflatten (map C.vlab (map injR ys)))
                    (unflatten (map C.vlab (map injR ysK))))
    → HomTerm (unflatten (map C.vlab (map injL P ++ map injR ys)))
              (unflatten (map C.vlab (map injL P ++ map injR ysK)))
  KCleanHead-gen P ys ysK kh =
    _≅_.to (BTC.uf++ (map injL P) (map injR ysK))
    ∘ (id {RpreObj P} ⊗₁ kh)
    ∘ _≅_.from (BTC.uf++ (map injL P) (map injR ys))

  ------------------------------------------------------------------------
  -- ### Shared abbreviations for the FIRE-core halves (split out to bound the
  -- per-definition typechecking memory: `kfac-fire-lhs` and `kfac-fire-rhs`
  -- elaborate independently).  All are deterministic functions of the FIRE
  -- data, so the common middle `kf-mid` is the SAME term in both halves.
  module _ (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
           (s : List (Fin C.nV))
           (rA : List (Fin C.nV)) (pA : s Perm.↭ C.ein (ψK e) ++ rA)
           (eqA : extract-prefix (C.ein (ψK e)) s ≡ just (rA , pA))
           (rK : List (Fin K.nV)) (pK : ys Perm.↭ K.ein e ++ rK)
           (eqK : extract-prefix (K.ein e) ys ≡ just (rK , pK))
           (pf1 : C.eout (ψK e) ++ rA Perm.↭ map injL P ++ map injR (K.eout e ++ rK))
           (pf  : s Perm.↭ map injL P ++ map injR ys)
    where
    private
      kf-eiB = C.ein  (ψK e)
      kf-eoB = C.eout (ψK e)
      kf-g   = C.elab (ψK e)
      kf-Pblk = map injL P
      kf-rgBlk = map injR rK
      kf-clean = kf-Pblk ++ kf-rgBlk

    -- the residual perm `clean ↭ rA` (the actual residual only ↭s clean).
    kf-r↭ : kf-clean Perm.↭ rA
    kf-r↭ = subst (kf-clean Perm.↭_) rA≡ (proj₂ (proj₂ (proj₂ cj)))
      where
        cj = clean-just e P ys s rK pK pf eqK
        rA≡ : proj₁ cj ≡ rA
        rA≡ = cong proj₁ (just-injective
                (trans (sym (proj₁ (proj₂ (proj₂ cj)))) eqA))

    -- the clean front-perm: `s ↭ eiB ++ clean`.
    kf-pA' : s Perm.↭ kf-eiB ++ kf-clean
    kf-pA' = Perm.↭-trans pA (PermProp.++⁺ˡ kf-eiB (Perm.↭-sym kf-r↭))

    kf-Box-sub : HomTerm
                   (unflatten (map C.vlab (map injL P ++ (kf-eiB ++ kf-rgBlk))))
                   (unflatten (map C.vlab (map injL P ++ (kf-eoB ++ kf-rgBlk))))
    kf-Box-sub = subst₂ HomTerm
                   (cong unflatten (whole-eq-K P kf-eiB kf-rgBlk))
                   (cong unflatten (whole-eq-K P kf-eoB kf-rgBlk))
                   (_≅_.to (unflatten-++-≅ (Pimg P) (map C.vlab kf-eoB ++ map C.vlab kf-rgBlk))
                    ∘ (id {RpreObj P} ⊗₁ box-of (map C.vlab kf-eiB) (map C.vlab kf-eoB)
                                               (map C.vlab kf-rgBlk) kf-g)
                    ∘ _≅_.from (unflatten-++-≅ (Pimg P) (map C.vlab kf-eiB ++ map C.vlab kf-rgBlk)))

    kf-pOut-L : kf-Pblk ++ (kf-eoB ++ kf-rgBlk) Perm.↭ kf-Pblk ++ map injR (K.eout e ++ rK)
    kf-pOut-L = Perm.↭-trans
                  (Perm.↭-trans (PermProp.shifts kf-Pblk kf-eoB {kf-rgBlk})
                                (PermProp.++⁺ˡ kf-eoB kf-r↭))
                  pf1
    kf-pIn-L : s Perm.↭ kf-Pblk ++ (kf-eiB ++ kf-rgBlk)
    kf-pIn-L = Perm.↭-trans kf-pA' (PermProp.shifts kf-eiB kf-Pblk {kf-rgBlk})

    -- the common middle term.
    kf-mid : HomTerm (unflatten (map C.vlab s))
                     (unflatten (map C.vlab (kf-Pblk ++ map injR (K.eout e ++ rK))))
    kf-mid = pvlC kf-pOut-L ∘ (kf-Box-sub ∘ pvlC kf-pIn-L)

  ------------------------------------------------------------------------
  -- ### `kfac-fire-lhs` — the LHS half: `pvlC pf1 ∘ fire-term … ≈ kf-mid`.
  kfac-fire-lhs
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (rA : List (Fin C.nV)) (pA : s Perm.↭ C.ein (ψK e) ++ rA)
      (eqA : extract-prefix (C.ein (ψK e)) s ≡ just (rA , pA))
      (rK : List (Fin K.nV)) (pK : ys Perm.↭ K.ein e ++ rK)
      (eqK : extract-prefix (K.ein e) ys ≡ just (rK , pK))
      (pCR : map injR ys Perm.↭ C.ein (ψK e) ++ map injR rK)
      (zEq : C.eout (ψK e) ++ map injR rK ≡ map injR (K.eout e ++ rK))
      (pf  : s Perm.↭ map injL P ++ map injR ys)
      (pf1 : C.eout (ψK e) ++ rA Perm.↭ map injL P ++ map injR (K.eout e ++ rK))
      (uniq : Unique s)
      (uniqK : Unique (map injL P ++ map injR (K.eout e ++ rK)))
    → pvlC pf1 ∘ fire-term C-hg (ψK e) s rA pA
      ≈Term kf-mid e P ys s rA pA eqA rK pK eqK pf1 pf
  kfac-fire-lhs e P ys s rA pA eqA rK pK eqK pCR zEq pf pf1 uniq uniqK = lhs≈mid
    where
      open FM.HomReasoning
      eiB = C.ein  (ψK e)
      eoB = C.eout (ψK e)
      g   = C.elab (ψK e)
      Pblk = map injL P
      rgBlk = map injR rK
      clean = Pblk ++ rgBlk
      ee = ψK e
      r↭ = kf-r↭ e P ys s rA pA eqA rK pK eqK pf1 pf
      pA' = kf-pA' e P ys s rA pA eqA rK pK eqK pf1 pf
      Box-sub = kf-Box-sub e P ys s rA pA eqA rK pK eqK pf1 pf
      pOut-L = kf-pOut-L e P ys s rA pA eqA rK pK eqK pf1 pf
      pIn-L = kf-pIn-L e P ys s rA pA eqA rK pK eqK pf1 pf

      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiB rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoB rgBlk)))
                 (box-of (map C.vlab eiB) (map C.vlab eoB) (map C.vlab rgBlk) g)

      module Si = Sin  eiB Pblk rgBlk
      module So = Sout eoB Pblk rgBlk

      eL  = map C.vlab eiB
      eoL = map C.vlab eoB
      pL  = map C.vlab Pblk
      rL  = map C.vlab rgBlk

      rsplit : map C.vlab clean ≡ pL ++ rL
      rsplit = map-++ C.vlab Pblk rgBlk

      box-clean = box-of eL eoL (map C.vlab clean) g

      box-split≡ : box-of eL eoL (pL ++ rL) g
                 ≡ subst₂ HomTerm
                     (cong unflatten (cong (eL  ++_) rsplit))
                     (cong unflatten (cong (eoL ++_) rsplit))
                     box-clean
      box-split≡ = sym (box-rest-rewrite eL eoL rsplit g)

      fmclean≡braid
        : fire-mid C-hg ee clean
          ≡ subst₂ HomTerm
              (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list))
              (box-of eL eoL (pL ++ rL) g)
      fmclean≡braid =
        sym
          (trans
            (cong (subst₂ HomTerm (cong unflatten (Si.dom-list))
                                  (cong unflatten (So.dom-list)))
                  box-split≡)
          (trans
            (subst₂-HomTerm-∘
               (cong unflatten (cong (eL  ++_) rsplit)) (cong unflatten (Si.dom-list))
               (cong unflatten (cong (eoL ++_) rsplit)) (cong unflatten (So.dom-list))
               box-clean)
            (cong₂ (λ p q → subst₂ HomTerm p q box-clean)
                   (objUIP _ (cong unflatten (sym (map-++ C.vlab eiB clean))))
                   (objUIP _ (cong unflatten (sym (map-++ C.vlab eoB clean)))))))

      to-eorg = _≅_.to   (BTC.uf++ Pblk (eoB ++ rgBlk))
      from-eirg = _≅_.from (BTC.uf++ Pblk (eiB ++ rgBlk))

      front-box-shifts
        : subst₂ HomTerm
            (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list))
            (box-of eL eoL (pL ++ rL) g)
          ≈Term pvlC (PermProp.shifts Pblk eoB {rgBlk})
                ∘ Box-sub
                ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})
      front-box-shifts = begin
          subst₂ HomTerm (cong unflatten (Si.dom-list)) (cong unflatten (So.dom-list))
            (box-of eL eoL (pL ++ rL) g)
            ≈⟨ box-braid-pvl eiB eoB Pblk rgBlk g ⟩
          (pvlC (PermProp.shifts Pblk eoB {rgBlk}) ∘ to-eorg)
            ∘ (id {RpreObj P} ⊗₁ BoxSub)
            ∘ (from-eirg ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk}))
            ≈⟨ FM.assoc ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ (to-eorg
               ∘ (id {RpreObj P} ⊗₁ BoxSub)
               ∘ (from-eirg ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})))
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ (to-eorg
               ∘ ((id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
               ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk}))
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ (to-eorg ∘ ((id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg))
            ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ ((to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub)) ∘ from-eirg)
            ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})
            ≈⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ (to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
            ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})
            ≈⟨ refl⟩∘⟨ ≈-Term-sym (box-prefix-BTC P eiB eoB rgBlk g) ⟩∘⟨refl ⟩
          pvlC (PermProp.shifts Pblk eoB {rgBlk})
            ∘ Box-sub
            ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk}) ∎

      fmclean-shifts
        : fire-mid C-hg ee clean
          ≈Term pvlC (PermProp.shifts Pblk eoB {rgBlk})
                ∘ Box-sub
                ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})
      fmclean-shifts = ≈-Term-trans (≡⇒≈Term fmclean≡braid) front-box-shifts

      out-collapse
        : pvlC pf1
          ∘ (pvlC (PermProp.++⁺ˡ eoB r↭) ∘ pvlC (PermProp.shifts Pblk eoB {rgBlk}))
          ≈Term pvlC pOut-L
      out-collapse =
        ≈-Term-sym
          (≈-Term-trans
            (pvlC-↭trans (Perm.↭-trans (PermProp.shifts Pblk eoB {rgBlk})
                                       (PermProp.++⁺ˡ eoB r↭)) pf1)
            (∘-resp-≈ ≈-Term-refl
              (pvlC-↭trans (PermProp.shifts Pblk eoB {rgBlk})
                           (PermProp.++⁺ˡ eoB r↭))))

      in-collapse
        : pvlC (PermProp.shifts eiB Pblk {rgBlk})
          ∘ (pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭)) ∘ pvlC pA)
          ≈Term pvlC pIn-L
      in-collapse =
        ≈-Term-sym
          (≈-Term-trans
            (pvlC-↭trans pA' (PermProp.shifts eiB Pblk {rgBlk}))
            (∘-resp-≈ ≈-Term-refl
              (pvlC-↭trans pA (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭)))))

      lhs≈mid : pvlC pf1 ∘ fire-term C-hg (ψK e) s rA pA
                ≈Term pvlC pOut-L ∘ (Box-sub ∘ pvlC pIn-L)
      lhs≈mid = begin
          pvlC pf1 ∘ (fire-mid C-hg ee rA ∘ pvlC pA)
            ≈⟨ refl⟩∘⟨ (fire-mid-equiv ⟩∘⟨refl) ⟩
          pvlC pf1
            ∘ ((pvlC (PermProp.++⁺ˡ eoB r↭)
                ∘ (fire-mid C-hg ee clean
                   ∘ pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭))))
               ∘ pvlC pA)
            ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (fmclean-shifts ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
          pvlC pf1
            ∘ ((pvlC (PermProp.++⁺ˡ eoB r↭)
                ∘ (((pvlC (PermProp.shifts Pblk eoB {rgBlk})
                     ∘ Box-sub
                     ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})))
                   ∘ pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭))))
               ∘ pvlC pA)
            ≈⟨ regroup ⟩
          (pvlC pf1
            ∘ (pvlC (PermProp.++⁺ˡ eoB r↭) ∘ pvlC (PermProp.shifts Pblk eoB {rgBlk})))
            ∘ Box-sub
            ∘ (pvlC (PermProp.shifts eiB Pblk {rgBlk})
               ∘ (pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭)) ∘ pvlC pA))
            ≈⟨ ∘-resp-≈ out-collapse (∘-resp-≈ ≈-Term-refl in-collapse) ⟩
          pvlC pOut-L ∘ (Box-sub ∘ pvlC pIn-L) ∎
        where
          fire-mid-equiv
            : fire-mid C-hg ee rA
              ≈Term pvlC (PermProp.++⁺ˡ eoB r↭)
                    ∘ (fire-mid C-hg ee clean
                       ∘ pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭)))
          fire-mid-equiv = FME.fire-mid-equivariant C-hg Kf ee r↭

          regroup
            : pvlC pf1
              ∘ ((pvlC (PermProp.++⁺ˡ eoB r↭)
                  ∘ (((pvlC (PermProp.shifts Pblk eoB {rgBlk})
                       ∘ Box-sub
                       ∘ pvlC (PermProp.shifts eiB Pblk {rgBlk})))
                     ∘ pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭))))
                 ∘ pvlC pA)
              ≈Term
              (pvlC pf1
                ∘ (pvlC (PermProp.++⁺ˡ eoB r↭) ∘ pvlC (PermProp.shifts Pblk eoB {rgBlk})))
              ∘ Box-sub
              ∘ (pvlC (PermProp.shifts eiB Pblk {rgBlk})
                 ∘ (pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭)) ∘ pvlC pA))
          regroup =
            ≈-Term-trans lhs→rn (≈-Term-sym rhs→rn)
            where
              A   = pvlC (PermProp.++⁺ˡ eoB r↭)
              S1  = pvlC (PermProp.shifts Pblk eoB {rgBlk})
              S2  = pvlC (PermProp.shifts eiB Pblk {rgBlk})
              A'  = pvlC (PermProp.++⁺ˡ eiB (Perm.↭-sym r↭))
              pAt = pvlC pA
              Pf1 = pvlC pf1
              B   = Box-sub
              rn = Pf1 ∘ (A ∘ (S1 ∘ (B ∘ (S2 ∘ (A' ∘ pAt)))))

              lhs→rn
                : Pf1 ∘ ((A ∘ ((S1 ∘ (B ∘ S2)) ∘ A')) ∘ pAt) ≈Term rn
              lhs→rn = begin
                  Pf1 ∘ ((A ∘ ((S1 ∘ (B ∘ S2)) ∘ A')) ∘ pAt)
                    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                  Pf1 ∘ (A ∘ ((S1 ∘ (B ∘ S2)) ∘ A') ∘ pAt)
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
                  Pf1 ∘ (A ∘ (S1 ∘ (B ∘ S2)) ∘ (A' ∘ pAt))
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
                  Pf1 ∘ (A ∘ (S1 ∘ ((B ∘ S2) ∘ (A' ∘ pAt))))
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
                  Pf1 ∘ (A ∘ (S1 ∘ (B ∘ (S2 ∘ (A' ∘ pAt))))) ∎

              rhs→rn
                : (Pf1 ∘ (A ∘ S1)) ∘ (B ∘ (S2 ∘ (A' ∘ pAt))) ≈Term rn
              rhs→rn = begin
                  (Pf1 ∘ (A ∘ S1)) ∘ (B ∘ (S2 ∘ (A' ∘ pAt)))
                    ≈⟨ FM.assoc ⟩
                  Pf1 ∘ ((A ∘ S1) ∘ (B ∘ (S2 ∘ (A' ∘ pAt))))
                    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                  Pf1 ∘ (A ∘ (S1 ∘ (B ∘ (S2 ∘ (A' ∘ pAt))))) ∎

  ------------------------------------------------------------------------
  -- ### `kfac-fire-rhs` — the RHS half: `kf-mid ≈ KCleanHead-gen … ∘ pvlC pf`.
  kfac-fire-rhs
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (rA : List (Fin C.nV)) (pA : s Perm.↭ C.ein (ψK e) ++ rA)
      (eqA : extract-prefix (C.ein (ψK e)) s ≡ just (rA , pA))
      (rK : List (Fin K.nV)) (pK : ys Perm.↭ K.ein e ++ rK)
      (eqK : extract-prefix (K.ein e) ys ≡ just (rK , pK))
      (pCR : map injR ys Perm.↭ C.ein (ψK e) ++ map injR rK)
      (zEq : C.eout (ψK e) ++ map injR rK ≡ map injR (K.eout e ++ rK))
      (pf  : s Perm.↭ map injL P ++ map injR ys)
      (pf1 : C.eout (ψK e) ++ rA Perm.↭ map injL P ++ map injR (K.eout e ++ rK))
      (uniq : Unique s)
      (uniqK : Unique (map injL P ++ map injR (K.eout e ++ rK)))
    → kf-mid e P ys s rA pA eqA rK pK eqK pf1 pf
      ≈Term KCleanHead-gen P ys (K.eout e ++ rK)
              (coeC {map injR ys} zEq
                 (fire-term C-hg (ψK e) (map injR ys) (map injR rK) pCR))
            ∘ pvlC pf
  kfac-fire-rhs e P ys s rA pA eqA rK pK eqK pCR zEq pf pf1 uniq uniqK = mid≈rhs
    where
      open FM.HomReasoning
      eiB = C.ein  (ψK e)
      eoB = C.eout (ψK e)
      g   = C.elab (ψK e)
      Pblk = map injL P
      rgBlk = map injR rK
      Box-sub = kf-Box-sub e P ys s rA pA eqA rK pK eqK pf1 pf
      pOut-L = kf-pOut-L e P ys s rA pA eqA rK pK eqK pf1 pf
      pIn-L = kf-pIn-L e P ys s rA pA eqA rK pK eqK pf1 pf

      BoxSub = subst₂ HomTerm
                 (cong unflatten (sym (map-++ C.vlab eiB rgBlk)))
                 (cong unflatten (sym (map-++ C.vlab eoB rgBlk)))
                 (box-of (map C.vlab eiB) (map C.vlab eoB) (map C.vlab rgBlk) g)

      pOut-R : Pblk ++ (eoB ++ rgBlk) Perm.↭ Pblk ++ map injR (K.eout e ++ rK)
      pOut-R = Perm.↭-reflexive (cong (Pblk ++_) zEq)
      pIn-R : s Perm.↭ Pblk ++ (eiB ++ rgBlk)
      pIn-R = Perm.↭-trans pf (PermProp.++⁺ (Perm.↭-refl {x = Pblk}) pCR)

      to-blk2-zEq
        : ∀ {B B' : List (Fin C.nV)} (eq : B ≡ B')
            (X : HomTerm (unflatten (map C.vlab (map injR ys)))
                         (unflatten (map C.vlab B)))
        → sidC (cong (Pblk ++_) eq)
          ∘ (_≅_.to (BTC.uf++ Pblk B) ∘ (id {RpreObj P} ⊗₁ X))
          ≈Term _≅_.to (BTC.uf++ Pblk B')
                ∘ (id {RpreObj P} ⊗₁ coeC {map injR ys} eq X)
      to-blk2-zEq refl X = idˡ

      mid≈rhs : pvlC pOut-L ∘ (Box-sub ∘ pvlC pIn-L)
                ≈Term KCleanHead-gen P ys (K.eout e ++ rK)
                        (coeC {map injR ys} zEq
                           (fire-term C-hg (ψK e) (map injR ys) (map injR rK) pCR))
                      ∘ pvlC pf
      mid≈rhs = begin
          pvlC pOut-L ∘ (Box-sub ∘ pvlC pIn-L)
            ≈⟨ ∘-resp-≈ (pvlC-coh uniqK pOut-L pOut-R)
                        (∘-resp-≈ ≈-Term-refl
                          (pvlC-coh (SU.Unique-resp-↭ pIn-L uniq) pIn-L pIn-R)) ⟩
          pvlC pOut-R ∘ (Box-sub ∘ pvlC pIn-R)
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ pvlC-↭trans pf (PermProp.++⁺ (Perm.↭-refl {x = Pblk}) pCR)) ⟩
          pvlC pOut-R ∘ (Box-sub ∘ (pvlC (PermProp.++⁺ (Perm.↭-refl {x = Pblk}) pCR) ∘ pvlC pf))
            ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
          pvlC pOut-R ∘ ((Box-sub ∘ pvlC (PermProp.++⁺ (Perm.↭-refl {x = Pblk}) pCR)) ∘ pvlC pf)
            ≈⟨ refl⟩∘⟨ (head-factor-K P eiB eoB rgBlk ys g pCR ⟩∘⟨refl) ⟩
          pvlC pOut-R
            ∘ ((_≅_.to (BTC.uf++ Pblk (eoB ++ rgBlk))
                ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))
                ∘ _≅_.from (BTC.uf++ Pblk (map injR ys)))
               ∘ pvlC pf)
            ≈⟨ pOut-R-as-sidC ⟩∘⟨refl ⟩
          sidC (cong (Pblk ++_) zEq)
            ∘ ((_≅_.to (BTC.uf++ Pblk (eoB ++ rgBlk))
                ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))
                ∘ _≅_.from (BTC.uf++ Pblk (map injR ys)))
               ∘ pvlC pf)
            ≈⟨ reassoc-out ⟩
          (sidC (cong (Pblk ++_) zEq)
            ∘ (_≅_.to (BTC.uf++ Pblk (eoB ++ rgBlk))
               ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))))
            ∘ (_≅_.from (BTC.uf++ Pblk (map injR ys)) ∘ pvlC pf)
            ≈⟨ to-blk2-zEq zEq (BoxSub ∘ pvlC pCR) ⟩∘⟨refl ⟩
          (_≅_.to (BTC.uf++ Pblk (map injR (K.eout e ++ rK)))
            ∘ (id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR)))
            ∘ (_≅_.from (BTC.uf++ Pblk (map injR ys)) ∘ pvlC pf)
            ≈⟨ reassoc-back ⟩
          KCleanHead-gen P ys (K.eout e ++ rK)
            (coeC {map injR ys} zEq (fire-term C-hg (ψK e) (map injR ys) (map injR rK) pCR))
            ∘ pvlC pf ∎
        where
          pOut-R-as-sidC : pvlC pOut-R ≈Term sidC (cong (Pblk ++_) zEq)
          pOut-R-as-sidC = pvlC-reflexive-cod (cong (Pblk ++_) zEq)

          reassoc-out
            : sidC (cong (Pblk ++_) zEq)
              ∘ ((_≅_.to (BTC.uf++ Pblk (eoB ++ rgBlk))
                  ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))
                  ∘ _≅_.from (BTC.uf++ Pblk (map injR ys)))
                 ∘ pvlC pf)
              ≈Term
              (sidC (cong (Pblk ++_) zEq)
                ∘ (_≅_.to (BTC.uf++ Pblk (eoB ++ rgBlk))
                   ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))))
              ∘ (_≅_.from (BTC.uf++ Pblk (map injR ys)) ∘ pvlC pf)
          reassoc-out = begin
              sidC (cong (Pblk ++_) zEq)
                ∘ ((to-y ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR)) ∘ from-y) ∘ pvlC pf)
                ≈⟨ refl⟩∘⟨ (FM.sym-assoc ⟩∘⟨refl) ⟩
              sidC (cong (Pblk ++_) zEq)
                ∘ (((to-y ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))) ∘ from-y) ∘ pvlC pf)
                ≈⟨ refl⟩∘⟨ FM.assoc ⟩
              sidC (cong (Pblk ++_) zEq)
                ∘ ((to-y ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR)))
                   ∘ (from-y ∘ pvlC pf))
                ≈⟨ FM.sym-assoc ⟩
              (sidC (cong (Pblk ++_) zEq)
                ∘ (to-y ∘ (id {RpreObj P} ⊗₁ (BoxSub ∘ pvlC pCR))))
                ∘ (from-y ∘ pvlC pf) ∎
            where
              to-y   = _≅_.to   (BTC.uf++ Pblk (eoB ++ rgBlk))
              from-y = _≅_.from (BTC.uf++ Pblk (map injR ys))

          reassoc-back
            : (_≅_.to (BTC.uf++ Pblk (map injR (K.eout e ++ rK)))
                ∘ (id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR)))
              ∘ (_≅_.from (BTC.uf++ Pblk (map injR ys)) ∘ pvlC pf)
              ≈Term
              KCleanHead-gen P ys (K.eout e ++ rK)
                (coeC {map injR ys} zEq (fire-term C-hg (ψK e) (map injR ys) (map injR rK) pCR))
              ∘ pvlC pf
          reassoc-back = begin
              (to-K ∘ (id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR)))
                ∘ (from-y ∘ pvlC pf)
                ≈⟨ FM.assoc ⟩
              to-K ∘ ((id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR))
                      ∘ (from-y ∘ pvlC pf))
                ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
              to-K ∘ ((id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR))
                      ∘ from-y)
                   ∘ pvlC pf
                ≈⟨ FM.sym-assoc ⟩
              (to-K ∘ (id {RpreObj P} ⊗₁ coeC {map injR ys} zEq (BoxSub ∘ pvlC pCR))
                    ∘ from-y)
                ∘ pvlC pf ∎
            where
              to-K   = _≅_.to   (BTC.uf++ Pblk (map injR (K.eout e ++ rK)))
              from-y = _≅_.from (BTC.uf++ Pblk (map injR ys))

  ------------------------------------------------------------------------
  -- ### `kfac-fire-core` — `kfac-fire` with the clean pure-R residual already
  -- in canonical form `map injR rK`.  Assembled from the two halves.
  kfac-fire-core
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (rA : List (Fin C.nV)) (pA : s Perm.↭ C.ein (ψK e) ++ rA)
      (eqA : extract-prefix (C.ein (ψK e)) s ≡ just (rA , pA))
      (rK : List (Fin K.nV)) (pK : ys Perm.↭ K.ein e ++ rK)
      (eqK : extract-prefix (K.ein e) ys ≡ just (rK , pK))
      (pCR : map injR ys Perm.↭ C.ein (ψK e) ++ map injR rK)
      (zEq : C.eout (ψK e) ++ map injR rK ≡ map injR (K.eout e ++ rK))
      (pf  : s Perm.↭ map injL P ++ map injR ys)
      (pf1 : C.eout (ψK e) ++ rA Perm.↭ map injL P ++ map injR (K.eout e ++ rK))
      (uniq : Unique s)
      (uniqK : Unique (map injL P ++ map injR (K.eout e ++ rK)))
    → pvlC pf1 ∘ fire-term C-hg (ψK e) s rA pA
      ≈Term KCleanHead-gen P ys (K.eout e ++ rK)
              (coeC {map injR ys} zEq
                 (fire-term C-hg (ψK e) (map injR ys) (map injR rK) pCR))
            ∘ pvlC pf
  kfac-fire-core e P ys s rA pA eqA rK pK eqK pCR zEq pf pf1 uniq uniqK =
    ≈-Term-trans
      (kfac-fire-lhs e P ys s rA pA eqA rK pK eqK pCR zEq pf pf1 uniq uniqK)
      (kfac-fire-rhs e P ys s rA pA eqA rK pK eqK pCR zEq pf pf1 uniq uniqK)

  ------------------------------------------------------------------------
  -- ### `kfac-fire` — the FIRE/FIRE/FIRE substantive head reconciliation.
  --
  -- The actual front box `fire-mid C (ψK e) rA ∘ pvlC pA` on the permuted
  -- stack `s` is moved past the `map injL P` prefix into `head-factor-K`'s
  -- prefix-held form, absorbing the residual-perm `r↭ : injL P ++ injR rK ↭
  -- rA` (box-rest-perm) en route, then reconciled to `KCleanHead-gen ∘ pvlC pf`
  -- by the keystone on the Unique codomains.
  kfac-fire
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (rA : List (Fin C.nV)) (pA : s Perm.↭ C.ein (ψK e) ++ rA)
      (eqA : extract-prefix (C.ein (ψK e)) s ≡ just (rA , pA))
      (rK : List (Fin K.nV)) (pK : ys Perm.↭ K.ein e ++ rK)
      (eqK : extract-prefix (K.ein e) ys ≡ just (rK , pK))
      (rCR : List (Fin C.nV)) (pCR : map injR ys Perm.↭ C.ein (ψK e) ++ rCR)
      (eqCR : extract-prefix (C.ein (ψK e)) (map injR ys) ≡ just (rCR , pCR))
      (zEq : C.eout (ψK e) ++ rCR ≡ map injR (K.eout e ++ rK))
      (pf  : s Perm.↭ map injL P ++ map injR ys)
      (pf1 : C.eout (ψK e) ++ rA Perm.↭ map injL P ++ map injR (K.eout e ++ rK))
      (uniq : Unique s)
      (uniqK : Unique (map injL P ++ map injR (K.eout e ++ rK)))
    → pvlC pf1 ∘ fire-term C-hg (ψK e) s rA pA
      ≈Term KCleanHead-gen P ys (K.eout e ++ rK)
              (coeC {map injR ys} zEq (fire-term C-hg (ψK e) (map injR ys) rCR pCR))
            ∘ pvlC pf
  kfac-fire e P ys s rA pA eqA rK pK eqK rCR pCR eqCR zEq pf pf1 uniq uniqK =
    -- collapse the CLEAN pure-R residual `rCR` to its canonical value
    -- `map injR rK` (exact, via the injective-lifting of `eqK`), matched at
    -- refl, then run the core with `rCR = map injR rK`.
    collapse rCR pCR eqCR zEq rCR≡
    where
      -- the pure-R residual is EXACTLY `map injR rK` (no perm wrinkle on the
      -- clean side — the injective `injR`-lifting preserves the residual).
      pureR-just
        : ∃[ q ] extract-prefix (C.ein (ψK e)) (map injR ys)
                   ≡ just (map injR rK , q)
      pureR-just =
        subst (λ ks → ∃[ q ] extract-prefix ks (map injR ys) ≡ just (map injR rK , q))
              (sym (ψK-ein e))
              (extract-prefix-via-injective-just injR
                 (λ {x} {y} → ↑ʳ-injective G.nV x y) (K.ein e) ys rK pK eqK)

      rCR≡ : rCR ≡ map injR rK
      rCR≡ = cong proj₁ (just-injective (trans (sym eqCR) (proj₂ pureR-just)))

      collapse
        : ∀ (rCR₀ : List (Fin C.nV))
            (pCR₀ : map injR ys Perm.↭ C.ein (ψK e) ++ rCR₀)
            (eqCR₀ : extract-prefix (C.ein (ψK e)) (map injR ys) ≡ just (rCR₀ , pCR₀))
            (zEq₀ : C.eout (ψK e) ++ rCR₀ ≡ map injR (K.eout e ++ rK))
            (rCR₀≡ : rCR₀ ≡ map injR rK)
        → pvlC pf1 ∘ fire-term C-hg (ψK e) s rA pA
          ≈Term KCleanHead-gen P ys (K.eout e ++ rK)
                  (coeC {map injR ys} zEq₀ (fire-term C-hg (ψK e) (map injR ys) rCR₀ pCR₀))
                ∘ pvlC pf
      collapse .(map injR rK) pCR₀ eqCR₀ zEq₀ refl =
        kfac-fire-core e P ys s rA pA eqA rK pK eqK pCR₀ zEq₀ pf pf1 uniq uniqK

  -- `Unique` of the clean form (the keystone codomain), via `Unique-resp-↭`.
  uniq-clean
    : ∀ {s : List (Fin C.nV)} {P : List (Fin G.nV)} {ys : List (Fin K.nV)}
    → Unique s → s Perm.↭ map injL P ++ map injR ys
    → Unique (map injL P ++ map injR ys)
  uniq-clean uniq pf = SU.Unique-resp-↭ pf uniq

  ------------------------------------------------------------------------
  -- The generalised dispatch.  All stuck `edge-step` projections are fresh
  -- pattern variables matched at the `EdgeStepR` witnesses.
  kfac-head-disp
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      {s'A : List (Fin C.nV)}
      {tA  : HomTerm (unflatten (map C.vlab s)) (unflatten (map C.vlab s'A))}
      {ysK : List (Fin K.nV)}
      {tKr : HomTerm (unflatten (map K.vlab ys)) (unflatten (map K.vlab ysK))}
      {zsC : List (Fin C.nV)}
      {tCR : HomTerm (unflatten (map C.vlab (map injR ys)))
                     (unflatten (map C.vlab zsC))}
      (zEq : zsC ≡ map injR ysK)
    → EdgeStepR C-hg s (ψK e) s'A tA
    → EdgeStepR K ys e ysK tKr
    → EdgeStepR C-hg (map injR ys) (ψK e) zsC tCR
    → (pf  : s Perm.↭ map injL P ++ map injR ys)
    → (pf1 : s'A Perm.↭ map injL P ++ map injR ysK)
    → Unique s
    → Unique (map injL P ++ map injR ysK)
    → pvlC pf1 ∘ tA
      ≈Term KCleanHead-gen P ys ysK (coeC {map injR ys} zEq tCR) ∘ pvlC pf

  -- ============ SKIP / SKIP / SKIP ============
  kfac-head-disp e P ys s zEq (skipR eqA) (skipR eqK) (skipR eqCR) pf pf1 uniq uniqK =
    begin
      pvlC pf1 ∘ id
        ≈⟨ idʳ ⟩
      pvlC pf1
        ≈⟨ pvlC-coh (SU.Unique-resp-↭ pf uniq) pf1 pf ⟩
      pvlC pf
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ pvlC pf
        ≈⟨ ≈-Term-sym head≈id ⟩∘⟨refl ⟩
      KCleanHead-gen P ys ys (coeC {map injR ys} zEq id) ∘ pvlC pf ∎
    where
      open FM.HomReasoning
      -- `coeC zEq id = id` (zEq : injR ys ≡ injR ys, collapsed by uipL).
      kh≈id : coeC {map injR ys} zEq id ≈Term id {unflatten (map C.vlab (map injR ys))}
      kh≈id = ≡⇒≈Term
                (trans (cong (λ z → coeC {map injR ys} z id) (uipL zEq refl)) refl)
      head≈id : KCleanHead-gen P ys ys (coeC {map injR ys} zEq id)
                ≈Term id {unflatten (map C.vlab (map injL P ++ map injR ys))}
      head≈id =
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl kh≈id) ≈-Term-refl))
          (≈-Term-sym (id-as-tensor (map injL P) (map injR ys)))

  -- ============ impossible cross-cases ============
  -- K skips but C-actual fires.
  kfac-head-disp e P ys s zEq (fireR rA pA eqA) (skipR eqK) _ pf pf1 uniq uniqK =
    ⊥-elim (just≢nothing (trans (sym eqA) (clean-nothing e P ys s pf eqK)))
  -- K fires but C-actual skips.
  kfac-head-disp e P ys s zEq (skipR eqA) (fireR rK pK eqK) _ pf pf1 uniq uniqK =
    ⊥-elim (just≢nothing
      (trans (sym (proj₁ (proj₂ (proj₂ (clean-just e P ys s rK pK pf eqK))))) eqA))
  -- K skips but C-pure-R fires.
  kfac-head-disp e P ys s zEq (skipR eqA) (skipR eqK) (fireR rCR pCR eqCR) pf pf1 uniq uniqK =
    ⊥-elim (just≢nothing (trans (sym eqCR) pureR-nothing))
    where
      pureR-nothing : extract-prefix (C.ein (ψK e)) (map injR ys) ≡ nothing
      pureR-nothing =
        subst (λ ks → extract-prefix ks (map injR ys) ≡ nothing)
              (sym (ψK-ein e))
              (extract-prefix-via-injective-nothing injR
                 (λ {x} {y} → ↑ʳ-injective G.nV x y) (K.ein e) ys eqK)
  -- K fires but C-pure-R skips.
  kfac-head-disp e P ys s zEq (fireR rA pA eqA) (fireR rK pK eqK) (skipR eqCR) pf pf1 uniq uniqK =
    ⊥-elim (just≢nothing (trans (sym (proj₂ pureR-just)) eqCR))
    where
      pureR-just
        : ∃[ q ] extract-prefix (C.ein (ψK e)) (map injR ys)
                   ≡ just (map injR rK , q)
      pureR-just =
        subst (λ ks → ∃[ q ] extract-prefix ks (map injR ys) ≡ just (map injR rK , q))
              (sym (ψK-ein e))
              (extract-prefix-via-injective-just injR
                 (λ {x} {y} → ↑ʳ-injective G.nV x y) (K.ein e) ys rK pK eqK)
  -- ============ FIRE / FIRE / FIRE (the substantive case) ============
  kfac-head-disp e P ys s zEq (fireR rA pA eqA) (fireR rK pK eqK) (fireR rCR pCR eqCR) pf pf1 uniq uniqK =
    kfac-fire e P ys s rA pA eqA rK pK eqK rCR pCR eqCR zEq pf pf1 uniq uniqK

  ------------------------------------------------------------------------
  -- ### `kfac-head` — the public per-K-edge HEAD reconciliation.  Instantiates
  -- `kfac-head-disp` at the three `edge-step-graph` relation witnesses (the
  -- C-actual head on `s`, the pure-K edge on `ys`, the C-pure-R head on
  -- `map injR ys`) + the real `zs1-emb` clean-stack agreement.
  --
  --   pvlC pf1 ∘ proj₂ (edge-step C (ψK e) s)
  --     ≈Term KCleanHead e P ys ∘ pvlC pf
  kfac-head
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (pf  : s Perm.↭ map injL P ++ map injR ys)
      (pf1 : proj₁ (edge-step C-hg s (ψK e))
             Perm.↭ map injL P ++ map injR (ys-step e ys))
      (uniq : Unique s)
      (uniqK : Unique (map injL P ++ map injR (ys-step e ys)))
    → pvlC pf1 ∘ proj₂ (edge-step C-hg s (ψK e))
      ≈Term KCleanHead e P ys ∘ pvlC pf
  kfac-head e P ys s pf pf1 uniq uniqK =
    kfac-head-disp e P ys s (zs1-emb e ys)
      (edge-step-graph C-hg s (ψK e))
      (edge-step-graph K ys e)
      (edge-step-graph C-hg (map injR ys) (ψK e))
      pf pf1 uniq uniqK

  ------------------------------------------------------------------------
  -- ### `kfac-gen` — the generalised K-side perm-tracking induction.
  --
  -- The K-mirror of `gblock-factor`.  Because the K-edges PREPEND their
  -- `eout` to the running stack, there is NO clean stack `≡` to thread (as
  -- the G-side does with `mixed-stack-G`); instead we track the ACTUAL
  -- running stack `s` together with a perm `pf : s ↭ map injL P ++ map injR
  -- ys` to the clean form, and a perm `Br` from the clean target stack to
  -- the actual post-run stack.  The structural induction mirrors
  -- `gblock-factor`: the head edge-step is reconciled by `kfac-head` (over
  -- the three `EdgeStepR` relation witnesses, internal to `kfac-head`), the
  -- tail by the IH, and the clean blocks merge through `KClean-cons`.
  --
  --   pe-termC (map ψK es) s ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf
  --
  -- The per-edge `pf1`/`res1`/`uniq1` are advanced exactly as in
  -- `gblock-factor` (`edge-step-↑ʳ-on-perm` for the perm,
  -- `edge-step-Reservoir≤1` for the freshness invariant).  Note that the
  -- IH's braid `Br1` and `kfac-gen`'s `Br` share domain and codomain
  -- DEFINITIONALLY (`pe-stackK (e∷es) ys = pe-stackK es (ys-step e ys)` and
  -- `pe-stackC (map ψK (e∷es)) s = pe-stackC (map ψK es) s1`), so `Br` is
  -- passed unchanged to the IH — no keystone reconcile of the braid needed.

  -- The per-edge clean perm `pf1 : s1 ↭ map injL P ++ map injR (ys-step e
  -- ys)`, read off `edge-step-↑ʳ-on-perm` (the per-edge K-prepend perm) at
  -- `pf`, transported along the `edge-step` `≡` projection onto `s1`.
  kfac-pf1
    : (e : Fin K.nE) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (pf : s Perm.↭ map injL P ++ map injR ys)
    → proj₁ (edge-step C-hg s (ψK e))
      Perm.↭ map injL P ++ map injR (ys-step e ys)
  kfac-pf1 e P ys s pf =
    subst (Perm._↭ (map injL P ++ map injR (ys-step e ys)))
          (sym (cong proj₁ eq))
          perm
    where
      data4 : ∃[ s' ] ∃[ t ]
                 edge-step C-hg s (ψK e) ≡ (s' , t)
               × s' Perm.↭ map injL P ++ map injR (ys-step e ys)
      data4 = edge-step-↑ʳ-on-perm G K e s P ys pf
      eq   = proj₁ (proj₂ (proj₂ data4))
      perm = proj₂ (proj₂ (proj₂ data4))

  kfac-gen
    : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
      (s : List (Fin C.nV))
      (pf : s Perm.↭ map injL P ++ map injR ys)
      (Br : map injL P ++ map injR (pe-stackK es ys)
            Perm.↭ pe-stackC (map (G.nE ↑ʳ_) es) s)
      (uniq : Unique s)
    → SUR.Reservoir≤1 (hTensor G K) (map (G.nE ↑ʳ_) es) s
    → pe-termC (map (G.nE ↑ʳ_) es) s
      ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf
  kfac-gen [] P ys s pf Br uniq res = begin
      id
        ≈⟨ ≈-Term-sym (pvlC-cancel uniq pf Br) ⟩
      pvlC Br ∘ pvlC pf
        ≈⟨ refl⟩∘⟨ ≈-Term-sym idˡ ⟩
      pvlC Br ∘ (id ∘ pvlC pf)
        ≈⟨ refl⟩∘⟨ (≈-Term-sym (KClean-nil P ys) ⟩∘⟨refl) ⟩
      pvlC Br ∘ (KClean [] P ys ∘ pvlC pf) ∎
    where open FM.HomReasoning
  kfac-gen (e ∷ es) P ys s pf Br uniq res = begin
      pe-termC (map (G.nE ↑ʳ_) es) s1 ∘ tH
        ≈⟨ IH ⟩∘⟨refl ⟩
      (pvlC Br ∘ KClean es P (ys-step e ys) ∘ pvlC pf1) ∘ tH
        ≈⟨ FM.assoc ⟩
      pvlC Br ∘ (KClean es P (ys-step e ys) ∘ pvlC pf1) ∘ tH
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      pvlC Br ∘ KClean es P (ys-step e ys) ∘ (pvlC pf1 ∘ tH)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ head ⟩
      pvlC Br ∘ KClean es P (ys-step e ys) ∘ (KCleanHead e P ys ∘ pvlC pf)
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      pvlC Br ∘ (KClean es P (ys-step e ys) ∘ KCleanHead e P ys) ∘ pvlC pf
        ≈⟨ refl⟩∘⟨ ≈-Term-sym (KClean-cons e es P ys) ⟩∘⟨refl ⟩
      pvlC Br ∘ KClean (e ∷ es) P ys ∘ pvlC pf ∎
    where
      open FM.HomReasoning
      s1 = proj₁ (edge-step C-hg s (ψK e))
      tH = proj₂ (edge-step C-hg s (ψK e))

      -- per-edge clean perm.
      pf1 : s1 Perm.↭ map injL P ++ map injR (ys-step e ys)
      pf1 = kfac-pf1 e P ys s pf

      -- reservoir / Unique advanced one edge for the tail.
      res1 : SUR.Reservoir≤1 C-hg (map (G.nE ↑ʳ_) es) s1
      res1 = SUR.edge-step-Reservoir≤1 C-hg (ψK e) (map (G.nE ↑ʳ_) es) s res

      uniq1 : Unique s1
      uniq1 = SUR.Reservoir≤1⇒Unique C-hg (map (G.nE ↑ʳ_) es) s1 res1

      uniqK1 : Unique (map injL P ++ map injR (ys-step e ys))
      uniqK1 = SU.Unique-resp-↭ pf1 uniq1

      -- tail (IH).  `Br` reused: `Br1` shares dom/cod definitionally.
      IH : pe-termC (map (G.nE ↑ʳ_) es) s1
           ≈Term pvlC Br ∘ KClean es P (ys-step e ys) ∘ pvlC pf1
      IH = kfac-gen es P (ys-step e ys) s1 pf1 Br uniq1 res1

      -- head (per-edge reconciliation).
      head : pvlC pf1 ∘ tH ≈Term KCleanHead e P ys ∘ pvlC pf
      head = kfac-head e P ys s pf pf1 uniq uniqK1

  -- ### `kblock-factor` — the K-side block factorization (the `s = clean,
  -- pf = ↭-refl, Br = ↭-sym KBraid` instance of `kfac-gen`).
  --
  --   coeC (mixed-stack-K es P ys) (pe-termC (map ψK es) clean) ≈Term KFactored
  --
  -- `mixed-stack-K es P ys = refl`, so the codomain `coeC` collapses to `id`;
  -- `pvlC ↭-refl ≈ id` collapses the input perm.
  kblock-factor
    : (es : List (Fin K.nE)) (P : List (Fin G.nV)) (ys : List (Fin K.nV))
    → SUR.Reservoir≤1 (hTensor G K) (map (G.nE ↑ʳ_) es)
        (map injL P ++ map injR ys)
    → coeC {map injL P ++ map injR ys} refl
        (pe-termC (map (G.nE ↑ʳ_) es) (map injL P ++ map injR ys))
      ≈Term KFactored es P ys
  kblock-factor es P ys res = begin
      coeC {clean} refl (pe-termC (map (G.nE ↑ʳ_) es) clean)
        ≈⟨ ≡⇒≈Term (cong (λ z → coeC {clean} z (pe-termC (map (G.nE ↑ʳ_) es) clean))
                         (uipL refl refl)) ⟩
      pe-termC (map (G.nE ↑ʳ_) es) clean
        ≈⟨ kfac-gen es P ys clean Perm.↭-refl (Perm.↭-sym (KBraid es P ys))
                    uniq-clean-s res ⟩
      pvlC (Perm.↭-sym (KBraid es P ys)) ∘ KClean es P ys ∘ pvlC (Perm.↭-refl {x = clean})
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pvl-refl ⟩
      pvlC (Perm.↭-sym (KBraid es P ys)) ∘ KClean es P ys ∘ id
        ≈⟨ refl⟩∘⟨ idʳ ⟩
      pvlC (Perm.↭-sym (KBraid es P ys)) ∘ KClean es P ys ∎
    where
      open FM.HomReasoning
      clean = map injL P ++ map injR ys

      uniq-clean-s : Unique clean
      uniq-clean-s = SUR.Reservoir≤1⇒Unique C-hg (map (G.nE ↑ʳ_) es) clean res

--------------------------------------------------------------------------------
-- ## `Linear H ⇒ Unique (cod H)` + algorithm extraction (sig-level).
--
-- `Linear⇒cod-Unique` and `decode-attempt-extract` now live in the shared
-- leaf `HomTermTransport` (imported at the top of this module).

--------------------------------------------------------------------------------
-- ## The main assembly — structure.
--
-- The final `decode-⊗-shape-inner`
--
--   decode (f ⊗₁ g)
--     ≈Term to(unflatten-++-≅ (flatten B) (flatten D))
--            ∘ (decode f ⊗₁ decode g)
--            ∘ from(unflatten-++-≅ (flatten A) (flatten C))
--
-- rests on two TERM-LEVEL mixed-stack factorizations — the term companions
-- of the STACK-only `process-edges-↑ˡ-on-mixed` / `process-edges-↑ʳ-on-perm`
-- (`DecodeAttempt`), which expose only `proj₁` (the stack) and leave the
-- per-edge term opaque behind an `∃[ t ]`:
--
--   * G-block (φ = injL): the G-edge block run from the MIXED dom
--     `C.dom = map injL G.dom ++ map injR K.dom` factors, modulo
--     `unflatten-++-≅`, as the CANONICAL G-block run on the pure image
--     `map injL G.dom` (which `EmbedData.TG.process-edges-term-emb` relabels
--     to `decode f`) tensored with `id` on the untouched `map injR K.dom`
--     suffix.  TERM companion of `process-edges-↑ˡ-on-mixed`.
--
--   * K-block (φ = injR): the K-edge block run from the post-G stack factors
--     as `id` on the `map injL sG-final` prefix tensored with the CANONICAL
--     K-block run on `map injR K.dom` (relabelled by
--     `EmbedData.TK.process-edges-term-emb` to `decode g`); the residual
--     reordering (K prepends its `eout` to the stack front, so the post-K
--     stack only `↭`s — not `≡`s — the disjoint `map injL sG-final ++
--     map injR sK-final`) is absorbed into the composite final-permute by the
--     keystone `permute-via-vlab-≈Term-coherence-K` (`uCcod`).  TERM companion
--     of `process-edges-↑ʳ-on-perm`.
--
-- Each is a STRUCTURAL INDUCTION on the edge list with a per-edge
-- `box-of`-suffix/-prefix `unflatten-++-≅` coherence reassociation
-- (`CIsoAssocFromCons.c-iso-assoc-from` + its `to`-dual); the final-permute
-- recombination into `decode f ⊗₁ decode g` is exactly the (PROVEN)
-- `BlockTensor.pvv-block-tensor`, with the `unflatten-++-≅ (flatten B/A)
-- (flatten D/C)` framing emerging from `domL-hTensor` / `codL-hTensor`.
--
-- Everything those two factorizations and the recombination depend on IS
-- proven and postulate-free above:
--
--   * `BlockTensor.pvv-block-tensor` — the permute-level block-tensor
--     decomposition `pvl (++⁺ p q) ≈ to ∘ (pvl p ⊗₁ pvl q) ∘ from` (the
--     genuinely-novel reusable kernel; combines `FME.permute-++⁺ˡ-slide`
--     with `BNB.frame-ext`, the iso cancellation, and `⊗`-interchange);
--   * `BlockTensor.pvv-++⁺ˡ-slide` — the vlab-bridged left `++⁺ˡ` slide;
--   * `EmbedData.{TG,TK}` — the G-/K-side `TermEmbed` gate instances
--     (φ = injL / injR), which relabel the canonical pure-image block runs
--     to `decode f` / `decode g`;
--   * `decode-attempt-extract` — exposing each decoder term as
--     `permute-via-vlab vlab perm ∘ process-term`;
--   * `Linear⇒cod-Unique` — the `Unique (cod)` witnesses the keystone
--     `permute-via-vlab-≈Term-coherence-K` consumes.

--------------------------------------------------------------------------------
-- ## The FINAL ⊗ assembly — `decode-⊗-shape-inner`.
--
-- Mirrors `DecodeComposeShape.decode-∘-shape-inner`'s final assembly, with the
-- ∘-machinery swapped for the ⊗-machinery: the composite C-run factors (via
-- `Inv.range-++` + `pe-term-++`) into the K-block ∘ G-block, each factored by
-- `kblock-factor` / `gblock-factor` into the `(· ⊗₁ ·)` framed forms, the
-- middle iso cancels, the two `⊗`-blocks merge (`⊗-∘-dist`), and the composite
-- final-permute collapses through `BlockTensor.pvv-block-tensor` into the
-- `unflatten-++-≅ (flatten B/A) (flatten D/C)` framing.

--------------------------------------------------------------------------------
-- ## The GENERIC ⊗ assembly — `decode-⊗-generic`.
--
-- The decoder-agnostic core of `decode-⊗-shape-inner`.  Abstracted over the
-- "decoder interface": the two sub-hypergraphs `G = ⟦f⟧` / `K = ⟦g⟧` (the
-- composite being `hTensor G K`), the decoder terms (`dec-f`/`dec-g`/`dec-fg`),
-- their `Linear` witnesses, the `decode-attempt … ≡ just t` totality data, the
-- `domL`/`codL ≡ flatten` boundary equalities, and the `dec-? ≡ subst₂ …
-- (proj₁ att-?)` defining equations.  Both the UNPRUNED `⟪_⟫`/`decode` and the
-- PRUNED `⟪_⟫ₚ`/`decodeP` decoders instantiate this (with all interface
-- equations holding `refl`), so the ~440-line assembly exists ONCE here.
--
-- All the heavy block machinery (`EmbedData`, `BlockFactor`, `BlockTensor`) is
-- generic in `G`/`K` and reused verbatim.
module DecodeShapeGeneric
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  {A B C₀ D : ObjTerm}
  (G K : Hypergraph FlatGen)
  (dec-f  : HomTerm (unflatten (flatten A))  (unflatten (flatten B)))
  (dec-g  : HomTerm (unflatten (flatten C₀)) (unflatten (flatten D)))
  (dec-fg : HomTerm (unflatten (flatten (A ⊗₀ C₀))) (unflatten (flatten (B ⊗₀ D))))
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K) (lin-C : Lin.Linear (hTensor G K))
  (att-f : Σ[ t ∈ HomTerm (unflatten (domL G)) (unflatten (codL G)) ]
             decode-attempt G ≡ just t)
  (att-g : Σ[ t ∈ HomTerm (unflatten (domL K)) (unflatten (codL K)) ]
             decode-attempt K ≡ just t)
  (att-C : Σ[ t ∈ HomTerm (unflatten (domL (hTensor G K))) (unflatten (codL (hTensor G K))) ]
             decode-attempt (hTensor G K) ≡ just t)
  (dDomf  : domL G ≡ flatten A)        (dCodf  : codL G ≡ flatten B)
  (dDomg  : domL K ≡ flatten C₀)       (dCodg  : codL K ≡ flatten D)
  (dDomfg : domL (hTensor G K) ≡ flatten (A ⊗₀ C₀))
  (dCodfg : codL (hTensor G K) ≡ flatten (B ⊗₀ D))
  (decf-eq  : dec-f  ≡ subst₂ HomTerm (cong unflatten dDomf)  (cong unflatten dCodf)  (proj₁ att-f))
  (decg-eq  : dec-g  ≡ subst₂ HomTerm (cong unflatten dDomg)  (cong unflatten dCodg)  (proj₁ att-g))
  (decfg-eq : dec-fg ≡ subst₂ HomTerm (cong unflatten dDomfg) (cong unflatten dCodfg) (proj₁ att-C))
  where
  open FaithfulnessResidual Kf using (permute-resp-≅↭)

  module G = Hypergraph G
  module K = Hypergraph K

  Cht : Hypergraph FlatGen
  Cht = hTensor G K
  module C = Hypergraph Cht


  open EmbedData objUIP Kf G K using (module TG; module TK)
  open BlockFactor objUIP Kf G K

  open FA.hTensor-impl G K using (injL; injR; vlab-c; vlab-injL; vlab-injR)
  open FM.HomReasoning

  ------------------------------------------------------------------
  -- Edge blocks (definitional: `range C.nE = gblk ++ kblk`).
  gblk = map (_↑ˡ K.nE) (range G.nE)
  kblk = map (G.nE ↑ʳ_) (range K.nE)

  ------------------------------------------------------------------
  -- The whole composite C-run, extracted with its final-permute.
  ext-C = decode-attempt-extract Cht
            (proj₁ (att-C))
            (proj₂ (att-C))
  perm-C = proj₁ ext-C
  ext-C-eq = proj₂ ext-C

  -- The two sub-decoders, extracted.
  ext-f = decode-attempt-extract G
            (proj₁ (att-f)) (proj₂ (att-f))
  perm-f = proj₁ ext-f
  ext-f-eq = proj₂ ext-f
  ext-g = decode-attempt-extract K
            (proj₁ (att-g)) (proj₂ (att-g))
  perm-g = proj₁ ext-g
  ext-g-eq = proj₂ ext-g

  -- Final G/K stacks.
  sG : List (Fin G.nV)
  sG = pe-stackG (range G.nE) G.dom
  sK : List (Fin K.nV)
  sK = pe-stackK (range K.nE) K.dom

  -- `C.dom = map injL G.dom ++ map injR K.dom` (definitional).
  after-G : List (Fin C.nV)
  after-G = pe-stackC gblk C.dom

  -- `after-G ≡ map injL sG ++ map injR K.dom` (G-edges leave a mixed
  -- stack with a pure-injL prefix and the untouched injR suffix).
  after-G-≡ : after-G ≡ map injL sG ++ map injR K.dom
  after-G-≡ = mixed-stack-G (range G.nE) G.dom K.dom

  after-K : List (Fin C.nV)
  after-K = pe-stackC kblk after-G

  -- `C.cod = map injL G.cod ++ map injR K.cod` (definitional).
  uCcod : Unique C.cod
  uCcod = Linear⇒cod-Unique Cht lin-C

  ------------------------------------------------------------------
  -- Reservoirs for each block, from `Linear Cht` via the provenance
  -- (`gblk ++ kblk ↭ range C.nE`) + `reservoir-split`.
  res-whole : SUR.Reservoir≤1 Cht (gblk ++ kblk) C.dom
  res-whole = SUR.dom-reservoir-prov Cht (proj₂ lin-C) (gblk ++ kblk)
                (Perm.↭-reflexive (sym (Inv.range-++ G.nE K.nE)))

  res-G : SUR.Reservoir≤1 Cht gblk C.dom
  res-G = SUR.reservoir-prefix Cht gblk kblk C.dom res-whole

  res-K-aG : SUR.Reservoir≤1 Cht kblk after-G
  res-K-aG = SUR.reservoir-split Cht gblk kblk C.dom res-whole

  -- The K-reservoir transported to the clean stack `map injL sG ++ map injR K.dom`.
  res-K : SUR.Reservoir≤1 Cht kblk (map injL sG ++ map injR K.dom)
  res-K = subst (SUR.Reservoir≤1 Cht kblk) after-G-≡ res-K-aG

  ------------------------------------------------------------------
  -- decode-extract bridges.
  decode-f-≈
    : dec-f ≈Term
      subst₂ HomTerm (cong unflatten (dDomf)) (cong unflatten (dCodf))
        (permute-via-vlab G.vlab perm-f ∘ proj₂ (process-edges G (range G.nE) G.dom))
  decode-f-≈ =
    ≈-Term-trans (≡⇒≈Term decf-eq)
      (≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (dDomf))
                                      (cong unflatten (dCodf)))
                     ext-f-eq))

  decode-g-≈
    : dec-g ≈Term
      subst₂ HomTerm (cong unflatten (dDomg)) (cong unflatten (dCodg))
        (permute-via-vlab K.vlab perm-g ∘ proj₂ (process-edges K (range K.nE) K.dom))
  decode-g-≈ =
    ≈-Term-trans (≡⇒≈Term decg-eq)
      (≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (dDomg))
                                      (cong unflatten (dCodg)))
                     ext-g-eq))

  decode-fg-≈
    : dec-fg ≈Term
      subst₂ HomTerm (cong unflatten (dDomfg))
                     (cong unflatten (dCodfg))
        (permute-via-vlab C.vlab perm-C
         ∘ proj₂ (process-edges Cht (range C.nE) C.dom))
  decode-fg-≈ =
    ≈-Term-trans (≡⇒≈Term decfg-eq)
      (≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (dDomfg))
                                      (cong unflatten (dCodfg)))
                     ext-C-eq))

  ----------------------------------------------------------------
  -- abbreviations for the whole-run / block C-level pieces.
  PC = permute-via-vlab C.vlab perm-C
  Pcomposite = pe-termC (range C.nE) C.dom
  Cdom-obj = unflatten (map C.vlab C.dom)

  gterm = pe-termC gblk C.dom
  kterm-aG = pe-termC kblk after-G
  pterm-f = proj₂ (process-edges G (range G.nE) G.dom)
  pterm-g = proj₂ (process-edges K (range K.nE) K.dom)

  Gpure = Lterm (range G.nE) G.dom
  Kpure = Kterm (range K.nE) K.dom
  clG = map injL sG ++ map injR K.dom

  ----------------------------------------------------------------
  -- ### C-level run-split + block factoring (mirror of compose steps 1–2).
  run-split-term
    : Pcomposite
      ≈Term coeC {C.dom} (sym (cong (λ es → pe-stackC es C.dom)
                                    (Inv.range-++ G.nE K.nE)))
                 (pe-termC (gblk ++ kblk) C.dom)
  run-split-term = elim (Inv.range-++ G.nE K.nE)
    where
      elim : ∀ {es : List (Fin C.nE)} (eq : range C.nE ≡ es)
           → Pcomposite
             ≈Term coeC {C.dom} (sym (cong (λ es' → pe-stackC es' C.dom) eq))
                        (pe-termC es C.dom)
      elim refl = ≈-Term-refl

  block-fact = pe-term-++ Cht gblk kblk C.dom

  absorb-coe
    : ∀ {ys} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        (perm : s' Perm.↭ ys)
        (t : HomTerm Cdom-obj (unflatten (map C.vlab s)))
    → permute-via-vlab C.vlab perm
        ∘ subst (λ z → HomTerm Cdom-obj (unflatten (map C.vlab z))) eq t
      ≈Term permute-via-vlab C.vlab (subst (λ z → z Perm.↭ ys) (sym eq) perm) ∘ t
  absorb-coe refl perm t = ≈-Term-refl

  eqRS = sym (cong (λ es → pe-stackC es C.dom) (Inv.range-++ G.nE K.nE))
  perm-C1 = subst (λ z → z Perm.↭ C.cod) (sym eqRS) perm-C

  step1 : PC ∘ Pcomposite
        ≈Term permute-via-vlab C.vlab perm-C1 ∘ pe-termC (gblk ++ kblk) C.dom
  step1 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl run-split-term)
                       (absorb-coe eqRS perm-C (pe-termC (gblk ++ kblk) C.dom))

  eqBF = sym (pe-stack-++ Cht gblk kblk C.dom)
  perm-C2 = subst (λ z → z Perm.↭ C.cod) (sym eqBF) perm-C1

  step2 : permute-via-vlab C.vlab perm-C1 ∘ pe-termC (gblk ++ kblk) C.dom
        ≈Term permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
  step2 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl block-fact)
                       (absorb-coe eqBF perm-C1 (kterm-aG ∘ gterm))

  ----------------------------------------------------------------
  -- ### Rebase the K-block + perm onto the CLEAN start stack `clG`.
  -- (`to-clean` at `eqM = after-G-≡`; `refl`-match collapses the coeC/subst.)
  perm-C2-cl : pe-stackC kblk clG Perm.↭ C.cod
  perm-C2-cl = subst (λ z → pe-stackC kblk z Perm.↭ C.cod) after-G-≡ perm-C2

  to-clean
    : ∀ (mid : List (Fin C.nV)) (eqM : after-G ≡ mid)
        (perm : pe-stackC kblk after-G Perm.↭ C.cod)
    → permute-via-vlab C.vlab perm ∘ (kterm-aG ∘ gterm)
      ≈Term permute-via-vlab C.vlab
              (subst (λ z → pe-stackC kblk z Perm.↭ C.cod) eqM perm)
            ∘ (pe-termC kblk mid ∘ coeC {C.dom} eqM gterm)
  to-clean .after-G refl perm = ≈-Term-refl

  step3 : permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
        ≈Term permute-via-vlab C.vlab perm-C2-cl
            ∘ (pe-termC kblk clG ∘ coeC {C.dom} after-G-≡ gterm)
  step3 = to-clean clG after-G-≡ perm-C2

  ----------------------------------------------------------------
  -- ### Substitute the two block factors.
  GF = GFactored (range G.nE) G.dom K.dom
  gterm-GF : coeC {C.dom} after-G-≡ gterm ≈Term GF
  gterm-GF = gblock-factor (range G.nE) G.dom K.dom res-G

  KF = KFactored (range K.nE) sG K.dom
  kterm-KF : pe-termC kblk clG ≈Term KF
  kterm-KF = kblock-factor (range K.nE) sG K.dom res-K

  step4 : permute-via-vlab C.vlab perm-C2-cl
            ∘ (pe-termC kblk clG ∘ coeC {C.dom} after-G-≡ gterm)
        ≈Term permute-via-vlab C.vlab perm-C2-cl ∘ (KF ∘ GF)
  step4 = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ kterm-KF gterm-GF)

  ----------------------------------------------------------------
  -- ### The pure-block C-terms, named, and the algebraic collapse.
  KBr = KBraid (range K.nE) sG K.dom
  KCl = KClean (range K.nE) sG K.dom

  -- KF = pvlC (↭-sym KBr) ∘ KCl   (definitional).
  -- combP : (injL sG ++ injR sK) ↭ C.cod, the post-braid perm.
  combP : (map injL sG ++ map injR sK) Perm.↭ C.cod
  combP = Perm.↭-trans (Perm.↭-sym KBr) perm-C2-cl

  pfL : map injL sG Perm.↭ map injL G.cod
  pfL = PermProp.map⁺ injL perm-f
  pfR : map injR sK Perm.↭ map injR K.cod
  pfR = PermProp.map⁺ injR perm-g

  -- `combP ≈ ++⁺ pfL pfR` on the Unique codomain (keystone).
  combP-coh : pvlC combP ≈Term pvlC (PermProp.++⁺ pfL pfR)
  combP-coh = pvlC-coh uCcod combP (PermProp.++⁺ pfL pfR)

  -- The whole middle collapse: `perm-C2-cl ∘ (KF ∘ GF) ≈ tensor-form`.
  to-cod = _≅_.to   (BTC.uf++ (map injL G.cod) (map injR K.cod))
  from-dom = _≅_.from (BTC.uf++ (map injL G.dom) (map injR K.dom))
  Gᶜ = pvlC pfL ∘ Gpure
  Kᶜ = pvlC pfR ∘ Kpure

  collapse
    : permute-via-vlab C.vlab perm-C2-cl ∘ (KF ∘ GF)
      ≈Term to-cod ∘ (Gᶜ ⊗₁ Kᶜ) ∘ from-dom
  collapse = begin
    pvlC perm-C2-cl ∘ (KF ∘ GF)
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    pvlC perm-C2-cl ∘ (pvlC (Perm.↭-sym KBr) ∘ (KCl ∘ GF))
      ≈⟨ FM.sym-assoc ⟩
    (pvlC perm-C2-cl ∘ pvlC (Perm.↭-sym KBr)) ∘ (KCl ∘ GF)
      ≈⟨ ≈-Term-sym (pvlC-↭trans (Perm.↭-sym KBr) perm-C2-cl) ⟩∘⟨refl ⟩
    pvlC combP ∘ (KCl ∘ GF)
      ≈⟨ refl⟩∘⟨ KCl∘GF ⟩
    pvlC combP ∘ (to-mid ∘ (Gpure ⊗₁ Kpure) ∘ from-dom)
      ≈⟨ FM.sym-assoc ⟩
    (pvlC combP ∘ to-mid) ∘ ((Gpure ⊗₁ Kpure) ∘ from-dom)
      ≈⟨ pvlC-collapse ⟩∘⟨refl ⟩
    (to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR)) ∘ ((Gpure ⊗₁ Kpure) ∘ from-dom)
      ≈⟨ FM.assoc ⟩
    to-cod ∘ ((pvlC pfL ⊗₁ pvlC pfR) ∘ ((Gpure ⊗₁ Kpure) ∘ from-dom))
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    to-cod ∘ (((pvlC pfL ⊗₁ pvlC pfR) ∘ (Gpure ⊗₁ Kpure)) ∘ from-dom)
      ≈⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl) ⟩
    to-cod ∘ ((Gᶜ ⊗₁ Kᶜ) ∘ from-dom) ∎
    where
      to-mid = _≅_.to (BTC.uf++ (map injL sG) (map injR sK))
      to-isG = _≅_.to (BTC.uf++ (map injL sG) (map injR K.dom))
      from-isG = _≅_.from (BTC.uf++ (map injL sG) (map injR K.dom))
      from-sK = _≅_.from (BTC.uf++ (map injL sG) (map injR sK))

      -- `KCl ∘ GF` middle iso cancellation + ⊗-merge.
      KCl∘GF
        : KCl ∘ GF ≈Term to-mid ∘ (Gpure ⊗₁ Kpure) ∘ from-dom
      KCl∘GF = begin
        (to-mid ∘ (id {RpreObj sG} ⊗₁ Kpure) ∘ from-isG)
          ∘ (to-isG ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom)
          ≈⟨ FM.assoc ⟩
        to-mid ∘ ((id {RpreObj sG} ⊗₁ Kpure) ∘ from-isG)
          ∘ (to-isG ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-mid ∘ (id {RpreObj sG} ⊗₁ Kpure) ∘ from-isG
          ∘ (to-isG ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-mid ∘ (id {RpreObj sG} ⊗₁ Kpure) ∘ (from-isG ∘ to-isG)
          ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (BTC.uf++ (map injL sG) (map injR K.dom)) ⟩∘⟨refl ⟩
        to-mid ∘ (id {RpreObj sG} ⊗₁ Kpure) ∘ id
          ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        to-mid ∘ (id {RpreObj sG} ⊗₁ Kpure) ∘ (Gpure ⊗₁ id {RsufObj K.dom}) ∘ from-dom
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-mid ∘ ((id {RpreObj sG} ⊗₁ Kpure) ∘ (Gpure ⊗₁ id {RsufObj K.dom})) ∘ from-dom
          ≈⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl) ⟩
        to-mid ∘ ((id ∘ Gpure) ⊗₁ (Kpure ∘ id)) ∘ from-dom
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ idʳ ⟩∘⟨refl ⟩
        to-mid ∘ (Gpure ⊗₁ Kpure) ∘ from-dom ∎

      -- `pvlC combP ∘ to-mid ≈ to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR)`.
      pvlC-collapse : pvlC combP ∘ to-mid ≈Term to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR)
      pvlC-collapse = begin
        pvlC combP ∘ to-mid
          ≈⟨ combP-coh ⟩∘⟨refl ⟩
        pvlC (PermProp.++⁺ pfL pfR) ∘ to-mid
          ≈⟨ BTC.pvv-block-tensor pfL pfR ⟩∘⟨refl ⟩
        (to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR) ∘ from-sK) ∘ to-mid
          ≈⟨ FM.assoc ⟩
        to-cod ∘ ((pvlC pfL ⊗₁ pvlC pfR) ∘ from-sK) ∘ to-mid
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR) ∘ (from-sK ∘ to-mid)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (BTC.uf++ (map injL sG) (map injR sK)) ⟩
        to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR) ∘ id
          ≈⟨ refl⟩∘⟨ idʳ ⟩
        to-cod ∘ (pvlC pfL ⊗₁ pvlC pfR) ∎

  ----------------------------------------------------------------
  -- ### Assemble the C-level transform.
  Pcomp-eq : PC ∘ Pcomposite ≈Term to-cod ∘ (Gᶜ ⊗₁ Kᶜ) ∘ from-dom
  Pcomp-eq =
    ≈-Term-trans step1
      (≈-Term-trans step2
        (≈-Term-trans step3
          (≈-Term-trans step4 collapse)))

  ----------------------------------------------------------------
  -- ### Boundary list-equalities (relabel injL/injR images to flatten).
  eAdom : map C.vlab (map injL G.dom) ≡ flatten A
  eAdom = trans (TG.vlab-φ G.dom) (dDomf)
  eCdom : map C.vlab (map injR K.dom) ≡ flatten C₀
  eCdom = trans (TK.vlab-φ K.dom) (dDomg)
  eBcod : map C.vlab (map injL G.cod) ≡ flatten B
  eBcod = trans (TG.vlab-φ G.cod) (dCodf)
  eDcod : map C.vlab (map injR K.cod) ≡ flatten D
  eDcod = trans (TK.vlab-φ K.cod) (dCodg)

  domFG = cong unflatten (dDomfg)
  codFG = cong unflatten (dCodfg)

  -- The `⊗₀`-shaped mid objects (the `to`/`from` domain/codomain).
  midⱽ = cong₂ _⊗₀_ (cong unflatten eBcod) (cong unflatten eDcod)
  midᵂ = cong₂ _⊗₀_ (cong unflatten eAdom) (cong unflatten eCdom)

  ----------------------------------------------------------------
  -- ### Iso boundary glue: `to-cod`/`from-dom` (BTC-framed) → raw.
  Xcod = map C.vlab (map injL G.cod)
  Ycod = map C.vlab (map injR K.cod)
  Xdom = map C.vlab (map injL G.dom)
  Ydom = map C.vlab (map injR K.dom)

  to-glue
    : subst₂ HomTerm midⱽ codFG to-cod
      ≡ _≅_.to (unflatten-++-≅ (flatten B) (flatten D))
  to-glue =
    trans (cong (subst₂ HomTerm midⱽ codFG)
                (BNB.to-subst₂-≅ bdyCod (unflatten-++-≅ Xcod Ycod)))
    (trans (subst₂-HomTerm-∘ refl midⱽ bdyCod codFG
              (_≅_.to (unflatten-++-≅ Xcod Ycod)))
    (trans (cong (λ z → subst₂ HomTerm midⱽ z (_≅_.to (unflatten-++-≅ Xcod Ycod)))
                 (objUIP (trans bdyCod codFG)
                         (cong unflatten (cong₂ _++_ eBcod eDcod))))
           (to-uf-cong eBcod eDcod)))
    where bdyCod = cong unflatten (sym (map-++ C.vlab (map injL G.cod) (map injR K.cod)))

  from-glue
    : subst₂ HomTerm domFG midᵂ from-dom
      ≡ _≅_.from (unflatten-++-≅ (flatten A) (flatten C₀))
  from-glue =
    trans (cong (subst₂ HomTerm domFG midᵂ)
                (BNB.from-subst₂-≅ bdyDom (unflatten-++-≅ Xdom Ydom)))
    (trans (subst₂-HomTerm-∘ bdyDom domFG refl midᵂ
              (_≅_.from (unflatten-++-≅ Xdom Ydom)))
    (trans (cong (λ z → subst₂ HomTerm z midᵂ (_≅_.from (unflatten-++-≅ Xdom Ydom)))
                 (objUIP (trans bdyDom domFG)
                         (cong unflatten (cong₂ _++_ eAdom eCdom))))
           (from-uf-cong eAdom eCdom)))
    where bdyDom = cong unflatten (sym (map-++ C.vlab (map injL G.dom) (map injR K.dom)))

  ----------------------------------------------------------------
  -- ### Fold `Gᶜ`/`Kᶜ` into `dec-f`/`dec-g` (gate + pvv-relabel).
  PF = permute-via-vlab G.vlab perm-f
  PG = permute-via-vlab K.vlab perm-g

  -- `coeC` re-expressed as a codomain-only `subst₂ HomTerm refl`.
  coeC-is-subst₂
    : ∀ {d s s' : List (Fin C.nV)} (eq : s ≡ s')
        (t : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s)))
    → coeC {d} eq t
      ≡ subst₂ HomTerm refl (cong unflatten (cong (map C.vlab) eq)) t
  coeC-is-subst₂ refl t = refl

  -- G-side twin: `subst₂ (vlab-φ G.dom)(vlab-φ G.cod) Gᶜ ≈ PF ∘ pterm-f`.
  peL = proc-stack-emb-L (range G.nE) G.dom
  M1G = cong unflatten
          (trans (cong (map C.vlab) (TG.proc-stack-emb (range G.nE) G.dom))
                 (TG.vlab-φ sG))

  Gpure-twin
    : subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (TG.vlab-φ sG))
        Gpure
      ≈Term pterm-f
  Gpure-twin =
    ≈-Term-trans
      (≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom))
                                      (cong unflatten (TG.vlab-φ sG)))
                     (coeC-is-subst₂ peL (pe-termC gblk (map injL G.dom)))))
    (≈-Term-trans
      (≡⇒≈Term (subst₂-HomTerm-∘
                  refl (cong unflatten (TG.vlab-φ G.dom))
                  (cong unflatten (cong (map C.vlab) peL))
                  (cong unflatten (TG.vlab-φ sG))
                  (pe-termC gblk (map injL G.dom))))
      (≈-Term-trans
        (subst₂-HomTerm-irrel objUIP
          (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (TG.vlab-φ G.dom))
          (trans (cong unflatten (cong (map C.vlab) peL))
                 (cong unflatten (TG.vlab-φ sG)))
          M1G
          (pe-termC gblk (map injL G.dom)))
        (TG.process-edges-term-emb (range G.nE) G.dom)))

  PF-twin
    : subst₂ HomTerm (cong unflatten (TG.vlab-φ sG)) (cong unflatten (TG.vlab-φ G.cod))
        (pvlC pfL)
      ≈Term PF
  PF-twin = pvv-relabel Kf injL C.vlab G.vlab vlab-injL perm-f

  Gᶜ-twin
    : subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (TG.vlab-φ G.cod))
        Gᶜ
      ≈Term PF ∘ pterm-f
  Gᶜ-twin =
    ≈-Term-trans
      (≡⇒≈Term (subst₂-HomTerm-∘-dist
                  (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (TG.vlab-φ sG))
                  (cong unflatten (TG.vlab-φ G.cod)) (pvlC pfL) Gpure))
      (∘-resp-≈ PF-twin Gpure-twin)

  Gpart : subst₂ HomTerm (cong unflatten eAdom) (cong unflatten eBcod) Gᶜ ≈Term dec-f
  Gpart =
    ≈-Term-trans
      (subst₂-HomTerm-irrel objUIP
        (cong unflatten eAdom)
        (trans (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (dDomf)))
        (cong unflatten eBcod)
        (trans (cong unflatten (TG.vlab-φ G.cod)) (cong unflatten (dCodf)))
        Gᶜ)
    (≈-Term-trans
      (≡⇒≈Term (sym (subst₂-HomTerm-∘
                      (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (dDomf))
                      (cong unflatten (TG.vlab-φ G.cod)) (cong unflatten (dCodf))
                      Gᶜ)))
    (≈-Term-trans
      (subst₂-resp-≈Term (cong unflatten (dDomf)) (cong unflatten (dCodf)) Gᶜ-twin)
      (≈-Term-sym decode-f-≈)))

  -- K-side, mirror with `injR`/`vlab-injR`/`TK`.
  peR = proc-stack-emb-R (range K.nE) K.dom
  M1K = cong unflatten
          (trans (cong (map C.vlab) (TK.proc-stack-emb (range K.nE) K.dom))
                 (TK.vlab-φ sK))

  Kpure-twin
    : subst₂ HomTerm (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (TK.vlab-φ sK))
        Kpure
      ≈Term pterm-g
  Kpure-twin =
    ≈-Term-trans
      (≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (TK.vlab-φ K.dom))
                                      (cong unflatten (TK.vlab-φ sK)))
                     (coeC-is-subst₂ peR (pe-termC kblk (map injR K.dom)))))
    (≈-Term-trans
      (≡⇒≈Term (subst₂-HomTerm-∘
                  refl (cong unflatten (TK.vlab-φ K.dom))
                  (cong unflatten (cong (map C.vlab) peR))
                  (cong unflatten (TK.vlab-φ sK))
                  (pe-termC kblk (map injR K.dom))))
      (≈-Term-trans
        (subst₂-HomTerm-irrel objUIP
          (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (TK.vlab-φ K.dom))
          (trans (cong unflatten (cong (map C.vlab) peR))
                 (cong unflatten (TK.vlab-φ sK)))
          M1K
          (pe-termC kblk (map injR K.dom)))
        (TK.process-edges-term-emb (range K.nE) K.dom)))

  PG-twin
    : subst₂ HomTerm (cong unflatten (TK.vlab-φ sK)) (cong unflatten (TK.vlab-φ K.cod))
        (pvlC pfR)
      ≈Term PG
  PG-twin = pvv-relabel Kf injR C.vlab K.vlab vlab-injR perm-g

  Kᶜ-twin
    : subst₂ HomTerm (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (TK.vlab-φ K.cod))
        Kᶜ
      ≈Term PG ∘ pterm-g
  Kᶜ-twin =
    ≈-Term-trans
      (≡⇒≈Term (subst₂-HomTerm-∘-dist
                  (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (TK.vlab-φ sK))
                  (cong unflatten (TK.vlab-φ K.cod)) (pvlC pfR) Kpure))
      (∘-resp-≈ PG-twin Kpure-twin)

  Kpart : subst₂ HomTerm (cong unflatten eCdom) (cong unflatten eDcod) Kᶜ ≈Term dec-g
  Kpart =
    ≈-Term-trans
      (subst₂-HomTerm-irrel objUIP
        (cong unflatten eCdom)
        (trans (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (dDomg)))
        (cong unflatten eDcod)
        (trans (cong unflatten (TK.vlab-φ K.cod)) (cong unflatten (dCodg)))
        Kᶜ)
    (≈-Term-trans
      (≡⇒≈Term (sym (subst₂-HomTerm-∘
                      (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (dDomg))
                      (cong unflatten (TK.vlab-φ K.cod)) (cong unflatten (dCodg))
                      Kᶜ)))
    (≈-Term-trans
      (subst₂-resp-≈Term (cong unflatten (dDomg)) (cong unflatten (dCodg)) Kᶜ-twin)
      (≈-Term-sym decode-g-≈)))

  ----------------------------------------------------------------
  -- ### Distribute the outer subst₂ and fold.
  -- subst₂ domFG codFG (to-cod ∘ (Gᶜ⊗Kᶜ) ∘ from-dom)
  --   ≡ subst₂ midⱽ codFG to-cod
  --       ∘ (subst₂ midᵂ midⱽ (Gᶜ⊗Kᶜ) ∘ subst₂ domFG midᵂ from-dom)
  dist
    : subst₂ HomTerm domFG codFG (to-cod ∘ (Gᶜ ⊗₁ Kᶜ) ∘ from-dom)
      ≡ subst₂ HomTerm midⱽ codFG to-cod
          ∘ (subst₂ HomTerm midᵂ midⱽ (Gᶜ ⊗₁ Kᶜ)
             ∘ subst₂ HomTerm domFG midᵂ from-dom)
  dist =
    trans (subst₂-HomTerm-∘-dist domFG midⱽ codFG to-cod ((Gᶜ ⊗₁ Kᶜ) ∘ from-dom))
          (cong (subst₂ HomTerm midⱽ codFG to-cod ∘_)
                (subst₂-HomTerm-∘-dist domFG midᵂ midⱽ (Gᶜ ⊗₁ Kᶜ) from-dom))

  mid-fold
    : subst₂ HomTerm midᵂ midⱽ (Gᶜ ⊗₁ Kᶜ) ≈Term dec-f ⊗₁ dec-g
  mid-fold =
    ≈-Term-trans
      (≡⇒≈Term (subst₂-⊗₁-dist
                  (cong unflatten eAdom) (cong unflatten eBcod)
                  (cong unflatten eCdom) (cong unflatten eDcod) Gᶜ Kᶜ))
      (⊗-resp-≈ Gpart Kpart)

  goal : dec-fg
       ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
            ∘ (dec-f ⊗₁ dec-g)
            ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C₀))
  goal =
    ≈-Term-trans decode-fg-≈
    (≈-Term-trans
      (subst₂-resp-≈Term domFG codFG Pcomp-eq)
    (≈-Term-trans
      (≡⇒≈Term dist)
      (∘-resp-≈ (≡⇒≈Term to-glue)
        (∘-resp-≈ mid-fold (≡⇒≈Term from-glue)))))

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where

  decode-⊗-shape-inner
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decode f ⊗₁ decode g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decode-⊗-shape-inner {A} {B} {C₀} {D} f g =
    DecodeShapeGeneric.goal objUIP Kf {A} {B} {C₀} {D} ⟪ f ⟫ ⟪ g ⟫
      (decode f) (decode g) (decode (f ⊗₁ g))
      (Lin.⟪⟫-Linear f) (Lin.⟪⟫-Linear g) (Lin.⟪⟫-Linear (f ⊗₁ g))
      (decode-attempt-Linear f) (decode-attempt-Linear g) (decode-attempt-Linear (f ⊗₁ g))
      (⟪⟫-domL f) (⟪⟫-codL f) (⟪⟫-domL g) (⟪⟫-codL g)
      (⟪⟫-domL (f ⊗₁ g)) (⟪⟫-codL (f ⊗₁ g))
      refl refl refl
