{-# OPTIONS --with-K #-}

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
--   * `EmbedData.{TG,TK}` — the G-/K-side `TermEmbed` gate instances
--     (φ = injL / injR, ψ = _↑ˡ K.nE / G.nE ↑ʳ_).
--   * `decode-attempt-extract`, `Linear⇒cod-Unique` — PROVEN (verbatim from
--     `DecodeComposeShape`).
--
-- RESIDUAL (NOT in this file; see the `## The main assembly — RESIDUAL`
-- section): `decode-⊗-shape-inner` itself, which needs the two TERM-LEVEL
-- mixed-stack factorizations (term companions of the STACK-only
-- `process-edges-↑ˡ-on-mixed` / `process-edges-↑ʳ-on-perm`).  Unlike the `∘`
-- case — where `C.dom = map injL G.dom` is a PURE φ-image and the gate applies
-- directly — the `⊗` blocks run on the DISJOINT MIXED dom
-- `map injL G.dom ++ map injR K.dom`, so each block term must first be sliced
-- as `(canonical run ⊗₁ id)` (resp. `(id ⊗₁ canonical run)`) by a per-edge
-- `box-of`-suffix/-prefix `unflatten-++-≅` coherence induction before the gate
-- and `pvv-block-tensor` apply.  These two inductions are the remaining work;
-- everything they need is proven here.  NO postulate, NO hole in this file.
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
        ; domL-hTensor; codL-hTensor
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
        ; process-edges-↑ˡ-on-mixed; process-edges-↑ʳ-on-perm)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (module TermEmbed; pe-term-++; pe-stack-++)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance sig as SE
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidEquivariant sig as FME
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData as BNB
open import Categories.APROP.Hypergraph.Completeness.Discharge.CIsoAssocFromCons sig
  using (c-iso-assoc-from)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of; box-of-cong; edge-step-graph)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.Hypergraph.ExtractPrefixEvalPhi
  using (eval-map⁺; cast-irrel; subst₂-FinBij-∘; ≈-fb-of-≡)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++; map-∘; map-cong; length-map; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueProp
open import Data.Maybe using (Maybe; just; nothing)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  -- `subst₂ FlatGen` cancellations (`--with-K`), copied from DecodeComposeShape.
  subst₂-FlatGen-cancel
    : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os')
        {is'' os'' : List X} (p' : is'' ≡ is') (q' : os'' ≡ os')
        (z : FlatGen is os)
    → subst₂ FlatGen (trans p (sym p')) (trans q (sym q')) z
      ≡ subst₂ FlatGen (sym p') (sym q') (subst₂ FlatGen p q z)
  subst₂-FlatGen-cancel refl refl refl refl z = refl

  subst₂-FlatGen-cancel′
    : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os') (z : FlatGen is os)
    → subst₂ FlatGen (sym p) (sym q) (subst₂ FlatGen p q z) ≡ z
  subst₂-FlatGen-cancel′ refl refl z = refl

  subst₂-HomTerm-irrel
    : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
      {A A' B B' : ObjTerm} (p p' : A ≡ A') (q q' : B ≡ B') (t : HomTerm A B)
    → subst₂ HomTerm p q t ≈Term subst₂ HomTerm p' q' t
  subst₂-HomTerm-irrel objUIP p p' q q' t =
    ≡⇒≈Term (cong₂ (λ x y → subst₂ HomTerm x y t) (objUIP p p') (objUIP q q'))

  subst₂-HomTerm-∘
    : ∀ {A A' A'' B B' B''}
        (p₁ : A ≡ A') (p₂ : A' ≡ A'') (q₁ : B ≡ B') (q₂ : B' ≡ B'') (t : HomTerm A B)
    → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ t)
      ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) t
  subst₂-HomTerm-∘ refl refl refl refl t = refl

  subst₂-resp-≈Term
    : ∀ {A A' B B'} (p : A ≡ A') (q : B ≡ B') {u v : HomTerm A B}
    → u ≈Term v → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
  subst₂-resp-≈Term refl refl u≈v = u≈v

  subst₂-HomTerm-∘-dist
    : ∀ {A A' B B' C C'}
        (p : A ≡ A') (q : B ≡ B') (r : C ≡ C')
        (f : HomTerm B C) (h : HomTerm A B)
    → subst₂ HomTerm p r (f ∘ h)
      ≡ subst₂ HomTerm q r f ∘ subst₂ HomTerm p q h
  subst₂-HomTerm-∘-dist refl refl refl f h = refl

  permute-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
      ≡ permute (subst₂ Perm._↭_ p q r)
  permute-subst₂ refl refl r = refl

  map⁺-subst₂
    : ∀ {a b} {A : Set a} {B : Set b} (h : A → B)
        {xs xs' ys ys' : List A} (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
    → PermProp.map⁺ h (subst₂ Perm._↭_ p q r)
      ≡ subst₂ Perm._↭_ (cong (map h) p) (cong (map h) q) (PermProp.map⁺ h r)
  map⁺-subst₂ h refl refl r = refl

  eval-subst₂-↭
    : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
        (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
    → eval-↭ (subst₂ Perm._↭_ p q r)
      ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
  eval-subst₂-↭ refl refl r = refl

  ------------------------------------------------------------------------
  -- Permute relabel-freeness (the `permute`-level twin), copied from
  -- DecodeComposeShape: for an injective, label-preserving embedding
  -- `φ` with `vJ ∘ φ ≗ vH`, the `vJ`-permute of the `φ`-relabel is the
  -- `vH`-permute, modulo the boundary transport.
  vlab-φ-lemma
    : ∀ {nH nJ : ℕ} (φ : Fin nH → Fin nJ) (vJ : Fin nJ → X) (vH : Fin nH → X)
        (veq : ∀ i → vJ (φ i) ≡ vH i) (s : List (Fin nH))
    → map vJ (map φ s) ≡ map vH s
  vlab-φ-lemma φ vJ vH veq s = trans (sym (map-∘ s)) (map-cong veq s)

  pvv-relabel
    : (Kf : FaithfulnessResidual)
      {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
      (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
      {xs ys : List (Fin nH)} (p : xs Perm.↭ ys)
    → subst₂ HomTerm
        (cong unflatten (vlab-φ-lemma φ vJ vH veq xs))
        (cong unflatten (vlab-φ-lemma φ vJ vH veq ys))
        (permute-via-vlab vJ (PermProp.map⁺ φ p))
      ≈Term permute-via-vlab vH p
  pvv-relabel Kf φ vJ vH veq {xs} {ys} p =
    ≈-Term-trans
      (≡⇒≈Term
        (permute-subst₂ (vlab-φ-lemma φ vJ vH veq xs)
                        (vlab-φ-lemma φ vJ vH veq ys)
                        (PermProp.map⁺ vJ (PermProp.map⁺ φ p))))
      (FaithfulnessResidual.permute-resp-≅↭ Kf
        (subst₂ Perm._↭_ (vlab-φ-lemma φ vJ vH veq xs)
                          (vlab-φ-lemma φ vJ vH veq ys)
                          (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
        (PermProp.map⁺ vH p)
        coincide)
    where
      px = vlab-φ-lemma φ vJ vH veq xs
      py = vlab-φ-lemma φ vJ vH veq ys

      coincide
        : eval-↭ (subst₂ Perm._↭_ px py (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
        ≈-fb eval-↭ (PermProp.map⁺ vH p)
      coincide =
        ≈-fb-of-≡
          (trans (eval-subst₂-↭ px py (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
          (trans (cong (subst₂ FinBij (cong length px) (cong length py))
                       (trans (eval-map⁺ vJ (PermProp.map⁺ φ p))
                              (cong (subst₂ FinBij
                                       (sym (length-map vJ (map φ xs)))
                                       (sym (length-map vJ (map φ ys))))
                                    (eval-map⁺ φ p))))
          (trans (cong (subst₂ FinBij (cong length px) (cong length py))
                       (subst₂-FinBij-∘
                          (sym (length-map φ xs)) (sym (length-map vJ (map φ xs)))
                          (sym (length-map φ ys)) (sym (length-map vJ (map φ ys)))
                          (eval-↭ p)))
          (trans (subst₂-FinBij-∘
                    (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                    (cong length px)
                    (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                    (cong length py)
                    (eval-↭ p))
          (trans (cast-irrel
                    (trans (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                           (cong length px))
                    (sym (length-map vH xs))
                    (trans (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                           (cong length py))
                    (sym (length-map vH ys))
                    (eval-↭ p))
                 (sym (eval-map⁺ vH p)))))))

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
      cancel-mid = begin
        (to-bd ∘ (id ⊗₁ pvl q) ∘ from-bc) ∘ (to-bc ∘ (pvl p ⊗₁ id) ∘ from-ac)
          ≈⟨ FM.assoc ⟩
        to-bd ∘ ((id ⊗₁ pvl q) ∘ from-bc) ∘ (to-bc ∘ (pvl p ⊗₁ id) ∘ from-ac)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-bd ∘ (id ⊗₁ pvl q) ∘ from-bc ∘ to-bc ∘ (pvl p ⊗₁ id) ∘ from-ac
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-bd ∘ (id ⊗₁ pvl q) ∘ (from-bc ∘ to-bc) ∘ (pvl p ⊗₁ id) ∘ from-ac
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (uf++ bs cs) ⟩∘⟨refl ⟩
        to-bd ∘ (id ⊗₁ pvl q) ∘ id ∘ (pvl p ⊗₁ id) ∘ from-ac
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        to-bd ∘ (id ⊗₁ pvl q) ∘ (pvl p ⊗₁ id) ∘ from-ac ∎

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

  ≡⇒≈Term' : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term' refl = ≈-Term-refl

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

  subst₂-as-conj
    : ∀ {a b c d : List X} (p : a ≡ b) (q : c ≡ d)
        (t : HomTerm (unflatten a) (unflatten c))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) t
      ≈Term subst-id-cod q ∘ t ∘ subst-id-dom p
  subst₂-as-conj refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)

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
          (∘-resp-≈ (≡⇒≈Term' s-eo⁻-as)
            (∘-resp-≈ ≈-Term-refl (≡⇒≈Term' s-ei-as)))

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
              regroup-L = begin
                to-eorg-R
                  ∘ ((to-eo-rg ⊗₁ id {UR})
                     ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)
                     ∘ (from-ei-rg ⊗₁ id {UR}))
                  ∘ from-eirg-R
                  -- push `to-eorg-R` into the inner block.
                  ≈⟨ FM.sym-assoc ⟩
                (to-eorg-R
                  ∘ ((to-eo-rg ⊗₁ id {UR})
                     ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)
                     ∘ (from-ei-rg ⊗₁ id {UR})))
                  ∘ from-eirg-R
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                ((to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}))
                  ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR}))
                  ∘ from-eirg-R
                  ≈⟨ FM.assoc ⟩
                (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}))
                  ∘ ((α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)
                     ∘ (from-ei-rg ⊗₁ id {UR}))
                  ∘ from-eirg-R
                  -- isolate `α⇐ ∘ G⊗id ∘ α⇒` so T-eo / F-ei brackets appear.
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}))
                  ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ FM.sym-assoc ⟩
                ((to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}))
                  ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒))
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                (to-eorg-R
                  ∘ ((to-eo-rg ⊗₁ id {UR})
                     ∘ (α⇐ ∘ (G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒)))
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
                (to-eorg-R
                  ∘ ((to-eo-rg ⊗₁ id {UR}) ∘ α⇐)
                     ∘ ((G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒))
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
                (to-eorg-R
                  ∘ (((to-eo-rg ⊗₁ id {UR}) ∘ α⇐) ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                     ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                ((to-eorg-R
                  ∘ (((to-eo-rg ⊗₁ id {UR}) ∘ α⇐) ∘ (G ⊗₁ id {Urg ⊗₀ UR})))
                     ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ (FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (((to-eorg-R
                  ∘ (((to-eo-rg ⊗₁ id {UR}) ∘ α⇐)))
                     ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                     ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ ((FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                ((((to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR})) ∘ α⇐)
                     ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                     ∘ α⇒)
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  -- now re-associate into the three target blocks.
                  ≈⟨ ((FM.assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (((to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
                     ∘ (G ⊗₁ id {Urg ⊗₀ UR}))
                     ∘ α⇒ {Uei} {Urg} {UR})
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                ((to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
                     ∘ ((G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒ {Uei} {Urg} {UR}))
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ FM.assoc ⟩
                (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
                  ∘ ((G ⊗₁ id {Urg ⊗₀ UR}) ∘ α⇒ {Uei} {Urg} {UR})
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
                  ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                  ∘ α⇒ {Uei} {Urg} {UR}
                  ∘ (from-ei-rg ⊗₁ id {UR})
                  ∘ from-eirg-R ∎

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

--------------------------------------------------------------------------------
-- ## `Linear H ⇒ Unique (cod H)` (sig-level), verbatim from DecodeComposeShape.

private
  open import Data.Nat.Base using () renaming (_≤_ to _≤ⁿ_)
  import Data.Nat.Properties as Nat
  open import Data.List using (concat; tabulate)

Linear⇒cod-Unique : (H : Hypergraph FlatGen) → Lin.Linear H → Unique (Hypergraph.cod H)
Linear⇒cod-Unique H (bal , bnd) = SU.count≤1⇒Unique cod-bnd
  where
    module H = Hypergraph H
    cod-bnd : ∀ v → Lin.count v H.cod ≤ⁿ 1
    cod-bnd v =
      Nat.≤-trans
        (Nat.≤-trans
          (Nat.m≤m+n (Lin.count v H.cod) (Lin.count v (concat (tabulate H.ein))))
          (Nat.≤-reflexive (sym (Lin.count-++ v H.cod (concat (tabulate H.ein))))))
        (Nat.≤-trans (Nat.≤-reflexive (sym (bal v))) (bnd v))

--------------------------------------------------------------------------------
-- ## Algorithm extraction (verbatim from DecodeComposeShape).

decode-attempt-extract
  : (H : Hypergraph FlatGen)
    (t : HomTerm (unflatten (domL H)) (unflatten (codL H)))
  → decode-attempt H ≡ just t
  → Σ[ perm ∈ proj₁ (process-all-edges H (Hypergraph.dom H)) Perm.↭ Hypergraph.cod H ]
      t ≡ permute-via-vlab (Hypergraph.vlab H) perm
            ∘ proj₂ (process-all-edges H (Hypergraph.dom H))
decode-attempt-extract H t eq
    with process-all-edges H (Hypergraph.dom H)
... | s_final , process-term
    with extract-exact (Hypergraph.cod H) s_final
...    | just perm with eq
...       | refl = perm , refl
decode-attempt-extract H t eq
    | s_final , process-term | nothing with eq
... | ()

--------------------------------------------------------------------------------
-- ## The main assembly — RESIDUAL.
--
-- The final `decode-⊗-shape-inner`
--
--   decode (f ⊗₁ g)
--     ≈Term to(unflatten-++-≅ (flatten B) (flatten D))
--            ∘ (decode f ⊗₁ decode g)
--            ∘ from(unflatten-++-≅ (flatten A) (flatten C))
--
-- is NOT YET assembled in this file.  It reduces, via the proven
-- infrastructure below, to two TERM-LEVEL mixed-stack factorizations — the
-- term companions of the STACK-only `process-edges-↑ˡ-on-mixed` /
-- `process-edges-↑ʳ-on-perm` (`DecodeAttempt`), which expose only `proj₁`
-- (the stack) and leave the per-edge term opaque behind an `∃[ t ]`:
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
