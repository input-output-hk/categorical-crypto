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
--   * `BoxAssoc.box-suffix` / `BoxAssoc.box-prefix` — PROVEN, postulate-free:
--     the two per-edge `box-of` reassociations.  `box-suffix` pulls an
--     untouched far suffix `R` out of a front-acting box's residual as
--     `(box … restG) ⊗₁ id_R`; `box-prefix` (its mirror) pulls an untouched
--     left prefix `P` out of a P-prefixed right-acting box as
--     `(P-prefixed box on einR) ⊗₁ id_restK`.  Both are Mac-Lane coherences
--     (⊗-functoriality + `α-comm` + `c-iso-assoc-from`/`-to` + bifunctor
--     mid-collapse); `box-prefix` is the term-companion per-edge step for
--     the K-block factorization, `box-suffix` for the G-block.
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
        ; process-edges-↑ˡ-on-mixed; process-edges-↑ʳ-on-perm
        ; edge-step-↑ˡ-on-mixed; edge-step-↑ˡ-on-mixed-just
        ; edge-step-↑ˡ-on-mixed-nothing)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↑ˡ-on-mixed-just; extract-prefix-↑ˡ-on-mixed-nothing
        ; extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
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

private
  module FM = Category FreeMonoidal

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

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
          (∘-resp-≈ (≡⇒≈Term' s-eo⁻-as)
            (∘-resp-≈ ≈-Term-refl (≡⇒≈Term' s-ei-as)))

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
              regroup-L = begin
                to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk})
                     ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)
                     ∘ (from-P-ei ⊗₁ id {Urk}))
                  ∘ from-Pei-rk
                  ≈⟨ FM.sym-assoc ⟩
                (to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk})
                     ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)
                     ∘ (from-P-ei ⊗₁ id {Urk})))
                  ∘ from-Pei-rk
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                ((to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}))
                  ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk}))
                  ∘ from-Pei-rk
                  ≈⟨ FM.assoc ⟩
                (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}))
                  ∘ ((α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)
                     ∘ (from-P-ei ⊗₁ id {Urk}))
                  ∘ from-Pei-rk
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}))
                  ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ FM.sym-assoc ⟩
                ((to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}))
                  ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒))
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                (to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk})
                     ∘ (α⇐ ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒)))
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
                (to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk}) ∘ α⇐)
                     ∘ ((id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒))
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ (refl⟩∘⟨ FM.sym-assoc) ⟩∘⟨refl ⟩
                (to-Peo-rk
                  ∘ (((to-P-eo ⊗₁ id {Urk}) ∘ α⇐) ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                     ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                ((to-Peo-rk
                  ∘ (((to-P-eo ⊗₁ id {Urk}) ∘ α⇐) ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))))
                     ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ (FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (((to-Peo-rk
                  ∘ ((to-P-eo ⊗₁ id {Urk}) ∘ α⇐))
                     ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                     ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ ((FM.sym-assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                ((((to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk})) ∘ α⇐)
                     ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                     ∘ α⇒)
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ ((FM.assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (((to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
                     ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk})))
                     ∘ α⇒ {UP} {Uei} {Urk})
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ FM.assoc ⟩∘⟨refl ⟩
                ((to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
                     ∘ ((id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒ {UP} {Uei} {Urk}))
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ FM.assoc ⟩
                (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
                  ∘ ((id {UP} ⊗₁ (G ⊗₁ id {Urk})) ∘ α⇒ {UP} {Uei} {Urk})
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
                  ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                  ∘ α⇒ {UP} {Uei} {Urk}
                  ∘ (from-P-ei ⊗₁ id {Urk})
                  ∘ from-Pei-rk ∎

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

--------------------------------------------------------------------------------
-- ## The G-side / K-side block factorizations — SHARED SCAFFOLDING.
--
-- SCAFFOLDING ONLY (proven, postulate-free, hole-free).  The two TERM
-- companions of the STACK-only `process-edges-↑ˡ-on-mixed` /
-- `process-edges-↑ʳ-on-perm` — `gblock-factor` (Milestone 2a) and
-- `kblock-factor` (Milestone 2b) — are NOT yet assembled (see the RESIDUAL
-- note at the end of the file).  This module fixes the framing convention
-- (`BTC.uf++`, matching `pvv-block-tensor`) and the factored-form shapes
-- (`GFactored`, `Lterm`) those two inductions land on, plus the stack
-- agreements (`mixed-stack-G`, `proc-stack-emb-L`) and the per-edge
-- `box-of` residual-rewrite (`box-rest-rewrite`) they consume.

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
  open EmbedData objUIP Kf G K using (module TG)

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

    -- `unflatten-++-≅`'s to/from under a BLOCK-1 list equality `r : L ≡ L'`
    -- (the `map-++ C.vlab` split between `box-suffix` and `BTC.uf++`),
    -- expressed as a single `subst` over the block-1 list.
    -- (`_≅_` from `Categories.Morphism`: `to : B ⇒ A`, `from : A ⇒ B`, so
    -- `to (uf L R) : ⊗ ⇒ (++)` and `from (uf L R) : (++) ⇒ ⊗`.)
    to-blk1 : ∀ (R L L' : List X) (r : L ≡ L')
            → subst (λ z → HomTerm (unflatten z ⊗₀ unflatten R) (unflatten (z ++ R)))
                    r (_≅_.to (unflatten-++-≅ L R))
              ≡ _≅_.to (unflatten-++-≅ L' R)
    to-blk1 R L .L refl = refl

    from-blk1 : ∀ (R L L' : List X) (r : L ≡ L')
              → subst (λ z → HomTerm (unflatten (z ++ R)) (unflatten z ⊗₀ unflatten R))
                      r (_≅_.from (unflatten-++-≅ L R))
                ≡ _≅_.from (unflatten-++-≅ L' R)
    from-blk1 R L .L refl = refl

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
  box-suffix-BTC eiBlk eoBlk rgBlk ys g =
    ≈-Term-trans (≡⇒≈Term decomp)
      (≈-Term-trans (subst₂-resp-≈Term (cong unflatten Cei) (cong unflatten Ceo)
                       (subst₂-resp-≈Term (cong unflatten Bei) (cong unflatten Beo)
                          (BoxAssoc.box-suffix
                             (map C.vlab eiBlk) (map C.vlab eoBlk)
                             (map C.vlab rgBlk) (Rys-flat ys) g)))
                    reframe)
    where
      eiL = map C.vlab eiBlk
      eoL = map C.vlab eoBlk
      rgL = map C.vlab rgBlk
      R   = Rys-flat ys

      Aei = sym (++-assoc eiL rgL R)
      Aeo = sym (++-assoc eoL rgL R)
      Bei = cong (_++ R) (sym (map-++ C.vlab eiBlk rgBlk))
      Beo = cong (_++ R) (sym (map-++ C.vlab eoBlk rgBlk))
      Cei = sym (map-++ C.vlab (eiBlk ++ rgBlk) (map injR ys))
      Ceo = sym (map-++ C.vlab (eoBlk ++ rgBlk) (map injR ys))

      -- The combined `subst₂ (whole-eq)` decomposes as the three layers
      -- `C ∘ B ∘ A` (via `subst₂-HomTerm-∘`, distributing `cong unflatten`
      -- over `trans`).
      decomp :
        subst₂ HomTerm
          (cong unflatten (whole-eq eiBlk rgBlk ys))
          (cong unflatten (whole-eq eoBlk rgBlk ys))
          (box-of eiL eoL (rgL ++ R) g)
        ≡ subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
            (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
               (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
                  (box-of eiL eoL (rgL ++ R) g)))
      decomp =
        trans
          (cong₂ (λ p q → subst₂ HomTerm p q (box-of eiL eoL (rgL ++ R) g))
                 (cong-whole eiBlk) (cong-whole eoBlk))
          (trans
            (sym (subst₂-HomTerm-∘
                    (cong unflatten Aei) (trans (cong unflatten Bei) (cong unflatten Cei))
                    (cong unflatten Aeo) (trans (cong unflatten Beo) (cong unflatten Ceo))
                    (box-of eiL eoL (rgL ++ R) g)))
            (sym (subst₂-HomTerm-∘
                    (cong unflatten Bei) (cong unflatten Cei)
                    (cong unflatten Beo) (cong unflatten Ceo)
                    (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
                       (box-of eiL eoL (rgL ++ R) g)))))
        where
          -- `cong unflatten (whole-eq) = trans (cong Aei)(trans (cong Bei)(cong Cei))`
          cong-whole : ∀ (lBlk : List (Fin C.nV))
                     → cong unflatten (whole-eq lBlk rgBlk ys)
                       ≡ trans (cong unflatten (sym (++-assoc (map C.vlab lBlk) rgL R)))
                           (trans (cong unflatten (cong (_++ R) (sym (map-++ C.vlab lBlk rgBlk))))
                                  (cong unflatten (sym (map-++ C.vlab (lBlk ++ rgBlk) (map injR ys)))))
          cong-whole lBlk =
            trans (sym (trans-cong {f = unflatten}
                          (sym (++-assoc (map C.vlab lBlk) rgL R))))
                  (cong (trans (cong unflatten (sym (++-assoc (map C.vlab lBlk) rgL R))))
                        (sym (trans-cong {f = unflatten}
                                (cong (_++ R) (sym (map-++ C.vlab lBlk rgBlk))))))

      reframe :
        subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
          (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
             (_≅_.to (unflatten-++-≅ (eoL ++ rgL) R)
               ∘ (box-of eiL eoL rgL g ⊗₁ id {unflatten R})
               ∘ _≅_.from (unflatten-++-≅ (eiL ++ rgL) R)))
        ≈Term _≅_.to (BTC.uf++ (eoBlk ++ rgBlk) (map injR ys))
              ∘ (subst₂ HomTerm
                   (cong unflatten (sym (map-++ C.vlab eiBlk rgBlk)))
                   (cong unflatten (sym (map-++ C.vlab eoBlk rgBlk)))
                   (box-of eiL eoL rgL g)
                   ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys))
      reframe = ≈-Term-sym (≡⇒≈Term rhs-≡)
        where
          eirg = eiBlk ++ rgBlk
          eorg = eoBlk ++ rgBlk
          UR   = unflatten R

          boxRg = box-of eiL eoL rgL g

          mpei = sym (map-++ C.vlab eiBlk rgBlk)
          mpeo = sym (map-++ C.vlab eoBlk rgBlk)

          -- `⊗₁ id`-subst push.
          ⊗-push
            : ∀ {a₁ a₂ b₁ b₂ : List X} (r₁ : a₁ ≡ a₂) (r₂ : b₁ ≡ b₂)
                (f : HomTerm (unflatten a₁) (unflatten b₁))
            → (subst₂ HomTerm (cong unflatten r₁) (cong unflatten r₂) f) ⊗₁ id {UR}
              ≡ subst₂ HomTerm
                  (cong (λ z → unflatten z ⊗₀ UR) r₁)
                  (cong (λ z → unflatten z ⊗₀ UR) r₂)
                  (f ⊗₁ id {UR})
          ⊗-push refl refl f = refl

          -- A `subst` over a 2-place `HomTerm` motive as a `subst₂`.
          subst-2 : ∀ {a b : List X} (f h : List X → ObjTerm) (r : a ≡ b)
                      (t : HomTerm (f a) (h a))
                  → subst (λ z → HomTerm (f z) (h z)) r t
                    ≡ subst₂ HomTerm (cong f r) (cong h r) t
          subst-2 f h refl t = refl

          -- to/from(BTC) re-expressed on the SPLIT raw blocks (to-BTC/from-BTC
          -- + the blk1 `map-++ C.vlab` reconciliation, recast via `subst-2`),
          -- combined to a single `subst₂` via `subst₂-HomTerm-∘`.
          to-eo-≡ :
            _≅_.to (BTC.uf++ eorg (map injR ys))
            ≡ subst₂ HomTerm
                (trans (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl)
                (trans (cong (λ z → unflatten (z ++ R)) mpeo) (cong unflatten Ceo))
                (_≅_.to (unflatten-++-≅ (eoL ++ rgL) R))
          to-eo-≡ =
            trans (to-BTC eorg (map injR ys))
            (trans (cong (subst₂ HomTerm refl (cong unflatten Ceo))
                         (trans (sym (to-blk1 R (eoL ++ rgL) (map C.vlab eorg) mpeo))
                                (subst-2 (λ z → unflatten z ⊗₀ UR) (λ z → unflatten (z ++ R))
                                   mpeo
                                   (_≅_.to (unflatten-++-≅ (eoL ++ rgL) R)))))
                   (subst₂-HomTerm-∘
                      (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl
                      (cong (λ z → unflatten (z ++ R)) mpeo) (cong unflatten Ceo)
                      (_≅_.to (unflatten-++-≅ (eoL ++ rgL) R))))

          from-ei-≡ :
            _≅_.from (BTC.uf++ eirg (map injR ys))
            ≡ subst₂ HomTerm
                (trans (cong (λ z → unflatten (z ++ R)) mpei) (cong unflatten Cei))
                (trans (cong (λ z → unflatten z ⊗₀ UR) mpei) refl)
                (_≅_.from (unflatten-++-≅ (eiL ++ rgL) R))
          from-ei-≡ =
            trans (from-BTC eirg (map injR ys))
            (trans (cong (subst₂ HomTerm (cong unflatten Cei) refl)
                         (trans (sym (from-blk1 R (eiL ++ rgL) (map C.vlab eirg) mpei))
                                (subst-2 (λ z → unflatten (z ++ R)) (λ z → unflatten z ⊗₀ UR)
                                   mpei
                                   (_≅_.from (unflatten-++-≅ (eiL ++ rgL) R)))))
                   (subst₂-HomTerm-∘
                      (cong (λ z → unflatten (z ++ R)) mpei) (cong unflatten Cei)
                      (cong (λ z → unflatten z ⊗₀ UR) mpei) refl
                      (_≅_.from (unflatten-++-≅ (eiL ++ rgL) R))))

          to-raw = _≅_.to   (unflatten-++-≅ (eoL ++ rgL) R)
          fr-raw = _≅_.from (unflatten-++-≅ (eiL ++ rgL) R)
          M      = boxRg ⊗₁ id {unflatten R}

          Qto = trans (cong (λ z → unflatten z ⊗₀ UR) mpeo) refl   -- to-eo-≡ dom
          Qfr = trans (cong (λ z → unflatten z ⊗₀ UR) mpei) refl   -- from-ei-≡ cod
          -- `cong (λ z → unflatten (z ++ R)) mp·` is `cong unflatten B·` modulo
          -- `cong-∘` (the `unflatten ∘ (_++ R)` composition).
          B'i = cong (λ z → unflatten (z ++ R)) mpei
          B'o = cong (λ z → unflatten (z ++ R)) mpeo
          P   = trans B'i (cong unflatten Cei)
          Rc  = trans B'o (cong unflatten Ceo)

          -- the middle box factor matches `subst₂ Qfr Qto M` modulo the two
          -- `trans _ refl` pads (`trans-reflʳ`).
          mid-≡ : (subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                    ⊗₁ id {RsufObj ys}
                  ≡ subst₂ HomTerm Qfr Qto M
          mid-≡ =
            trans (⊗-push mpei mpeo boxRg)
                  (cong₂ (λ p q → subst₂ HomTerm p q M)
                         (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpei)))
                         (sym (trans-reflʳ (cong (λ z → unflatten z ⊗₀ UR) mpeo))))

          rhs-≡ :
            _≅_.to (BTC.uf++ eorg (map injR ys))
              ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                   ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ eirg (map injR ys))
            ≡ subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                (subst₂ HomTerm (cong unflatten Bei) (cong unflatten Beo)
                   (to-raw ∘ M ∘ fr-raw))
          rhs-≡ = ≡R.begin
              _≅_.to (BTC.uf++ eorg (map injR ys))
                ∘ ((subst₂ HomTerm (cong unflatten mpei) (cong unflatten mpeo) boxRg)
                     ⊗₁ id {RsufObj ys})
                ∘ _≅_.from (BTC.uf++ eirg (map injR ys))
                -- Step 1: rewrite the three BTC factors to substituted raw.
                ≡R.≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) to-eo-≡ mid-≡ from-ei-≡ ⟩
              subst₂ HomTerm Qto Rc to-raw
                ∘ subst₂ HomTerm Qfr Qto M
                ∘ subst₂ HomTerm P Qfr fr-raw
                -- Step 2: recombine the M / from factors.
                ≡R.≡⟨ cong (λ w → subst₂ HomTerm Qto Rc to-raw ∘ w)
                        (sym (subst₂-HomTerm-∘-dist P Qfr Qto M fr-raw)) ⟩
              subst₂ HomTerm Qto Rc to-raw
                ∘ subst₂ HomTerm P Qto (M ∘ fr-raw)
                -- Step 3: recombine the to factor.
                ≡R.≡⟨ sym (subst₂-HomTerm-∘-dist P Qto Rc to-raw (M ∘ fr-raw)) ⟩
              subst₂ HomTerm P Rc (to-raw ∘ M ∘ fr-raw)
                -- Step 4: re-nest the combined `subst₂` into `Cei'∘B'·` form.
                ≡R.≡⟨ sym (subst₂-HomTerm-∘
                          B'i (cong unflatten Cei)
                          B'o (cong unflatten Ceo)
                          (to-raw ∘ M ∘ fr-raw)) ⟩
              subst₂ HomTerm (cong unflatten Cei) (cong unflatten Ceo)
                (subst₂ HomTerm B'i B'o (to-raw ∘ M ∘ fr-raw))
                -- Step 5: `B'·` ≡ `cong unflatten B·` (the `cong-∘` bridge).
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
      cancel-mid = begin
        (to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ from-eirg)
          ∘ (to-eirg ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs)
          ≈⟨ FM.assoc ⟩
        to-eorg ∘ ((BoxSub ⊗₁ id {RsufObj ys}) ∘ from-eirg)
          ∘ (to-eirg ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ from-eirg
          ∘ to-eirg ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ (from-eirg ∘ to-eirg)
          ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (BTC.uf++ (eiBlk ++ rgBlk) (map injR ys)) ⟩∘⟨refl ⟩
        to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys}) ∘ id
          ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        to-eorg ∘ (BoxSub ⊗₁ id {RsufObj ys})
          ∘ (pvlC p ⊗₁ id {RsufObj ys}) ∘ from-xs ∎

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
      cancel-mid = begin
        (to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
          ∘ (to-eirg ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys)
          ≈⟨ FM.assoc ⟩
        to-eorg ∘ ((id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg)
          ∘ (to-eirg ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ from-eirg
          ∘ to-eirg ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ (from-eirg ∘ to-eirg)
          ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (BTC.uf++ (map injL P) (eiBlk ++ rgBlk)) ⟩∘⟨refl ⟩
        to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub) ∘ id
          ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        to-eorg ∘ (id {RpreObj P} ⊗₁ BoxSub)
          ∘ (id {RpreObj P} ⊗₁ pvlC q) ∘ from-ys ∎

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
              ≈⟨ FM.assoc ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ ((Lterm es xs' ⊗₁ id {RsufObj ys}) ∘ _≅_.from (BTC.uf++ (map injL xs') Rys))
              ∘ (_≅_.to (BTC.uf++ (map injL xs') Rys)
                 ∘ (Lhead ⊗₁ id {RsufObj ys})
                 ∘ _≅_.from (BTC.uf++ Lxs Rys))
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ (Lterm es xs' ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ (map injL xs') Rys)
              ∘ _≅_.to (BTC.uf++ (map injL xs') Rys)
              ∘ (Lhead ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ (Lterm es xs' ⊗₁ id {RsufObj ys})
              ∘ (_≅_.from (BTC.uf++ (map injL xs') Rys)
                 ∘ _≅_.to (BTC.uf++ (map injL xs') Rys))
              ∘ (Lhead ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (BTC.uf++ (map injL xs') Rys) ⟩∘⟨refl ⟩
            _≅_.to (BTC.uf++ Lxs'' Rys)
              ∘ (Lterm es xs' ⊗₁ id {RsufObj ys})
              ∘ id
              ∘ (Lhead ⊗₁ id {RsufObj ys})
              ∘ _≅_.from (BTC.uf++ Lxs Rys)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
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
