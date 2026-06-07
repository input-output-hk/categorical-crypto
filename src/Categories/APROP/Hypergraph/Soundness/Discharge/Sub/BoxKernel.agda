{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- BOX KERNEL: the self-contained `unflatten-++-≅` box-reassociation cone,
-- extracted verbatim from `Sub/DecodeTensorShape.agda` (it lives here so the
-- standalone validation lemma `Sub/SeparableSpike.agda` can reuse
-- `box-suffix-framed` WITHOUT importing the heavyweight `DecodeTensorShape`).
--
-- Three mutually self-contained modules (no `EmbedData`/`FaithfulnessResidual`
-- dependency):
--
--   * `BlockTensor.pvv-block-tensor` — the `_⊗₁_` analogue of the `∘`-case
--     final-permute collapse:
--       `pvl (++⁺ p q) ≈ to(uf++ bs ds) ∘ (pvl p ⊗₁ pvl q) ∘ from(uf++ as cs)`.
--     A left `++⁺ˡ` slide + right `++⁺ʳ` slide + middle iso-cancellation +
--     `⊗`-interchange.
--   * `BoxAssoc.box-suffix` / `box-prefix` — per-edge `box-of`
--     reassociations pulling an untouched far suffix (resp. left prefix)
--     out of a box as `(box …) ⊗₁ id` (resp. `id ⊗₁ box …`).  Mac-Lane
--     coherences (⊗-functoriality + α-comm + c-iso-assoc + bifunctor
--     mid-collapse).  Plus `box-braid` — the σ-mirror of `box-suffix`: a
--     front-acting box on `P ++ rest` factors as the box held AFTER `P`,
--     conjugated by block-swap braids.  Uses one-box symmetry-naturality +
--     σ∘σ≈id + α-coherence (NOT the two-box `nf-bracket` kernel).
--   * `BlockBoxSuffix.box-suffix-framed` — `BoxAssoc.box-suffix` reframed into
--     the `BlockTensor vlab` `uf++` convention, generic in the suffix block.
--
-- Postulate-free, hole-free, `--safe`.  Parameterised exactly like
-- `DecodeTensorShape`.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BoxKernel
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab; permute)
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidEquivariant sig as FME
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData _≟X_ as BNB
open import Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons sig
  using (c-iso-assoc-from)
open import Categories.APROP.Hypergraph.Soundness.UnflattenMonoidal sig
  using (c-iso-assoc-to; cancel-mid-iso; conj-lemma; bridge-dom; bridge-cod
        ; subst-2)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeStepRelation sig
  using (box-of)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-cong; trans-reflʳ; cong-∘)

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using ( subst₂-resp-≈Term
        ; subst₂-HomTerm-∘
        ; subst₂-HomTerm-∘-dist
        ; permute-subst₂ )

private
  module FM = Category FreeMonoidal

-- Library iso-cancellation combinators (agda-categories), for the
-- `unflatten-++-≅` `from ∘ to ≈ id` eliminations.
open import Categories.Morphism.Reasoning FreeMonoidal using (cancelˡ; cancelʳ)

--------------------------------------------------------------------------------
-- ## The block-tensor decomposition of `permute`: `permute (++⁺ p q)`
-- slides through `unflatten-++-≅` as the tensor `permute p ⊗₁ permute q`,
-- built from the LEFT slide + a RIGHT slide composed through the middle
-- iso-cancellation and `⊗`-interchange.

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
  -- vlab-bridged left slide, from `FME.permute-++⁺ˡ-slide` + the
  -- `map⁺-++⁺ˡ`/`map-++` reconciliation (mirrors BNB's right-side
  -- `pvv-++⁺ʳ` + `frame-ext`).
  private
    -- `permute-via-vlab vlab (++⁺ˡ ws q)` re-expressed via the X-level
    -- `permute (++⁺ˡ (map vlab ws) (map⁺ vlab q))`.
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
      ≈⟨ BNB.frame-transport pAs pBs
           rawTO (id ⊗₁ permute (PermProp.map⁺ vlab q)) rawFROM to-eq refl from-eq ⟩
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
  -- THE BLOCK-TENSOR DECOMPOSITION.  Since
  -- `pvl (++⁺ p q) = pvl (++⁺ˡ bs q) ∘ pvl (++⁺ʳ cs p)`, slide each, cancel
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

  -- `from`-side associativity kernel.
  assoc-from = c-iso-assoc-from

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
  -- Shared associativity re-bracketing for `box-suffix`/`box-prefix`:
  -- `T ∘ (A ∘ (αc ∘ X ∘ ac) ∘ B) ∘ F ≈ (T ∘ A ∘ αc) ∘ X ∘ ac ∘ B ∘ F`.
  -- Pure associativity, fully generic in the arguments.
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
  -- Shared mid-reshuffle for `box-suffix`/`box-prefix`'s `regroup-mid`:
  -- `(a ∘ b ∘ c) ∘ M ∘ (d ∘ e ∘ f) ≈ a ∘ b ∘ (c ∘ M ∘ d) ∘ e ∘ f`.
  -- Pure associativity, fully generic in the arguments (mirror-shared).
  bracket-mid
    : ∀ {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ : ObjTerm}
        (a : HomTerm O₆ O₇) (b : HomTerm O₅ O₆) (c : HomTerm O₄ O₅)
        (M : HomTerm O₃ O₄) (d : HomTerm O₂ O₃)
        (e : HomTerm O₁ O₂) (f : HomTerm O₀ O₁)
    → (a ∘ b ∘ c) ∘ M ∘ (d ∘ e ∘ f)
      ≈Term a ∘ b ∘ (c ∘ M ∘ d) ∘ e ∘ f
  bracket-mid a b c M d e f = begin
      (a ∘ b ∘ c) ∘ M ∘ (d ∘ e ∘ f)
        ≈⟨ FM.assoc ⟩
      a ∘ (b ∘ c) ∘ M ∘ (d ∘ e ∘ f)
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      a ∘ b ∘ c ∘ M ∘ (d ∘ e ∘ f)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      a ∘ b ∘ (c ∘ M) ∘ (d ∘ e ∘ f)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      a ∘ b ∘ ((c ∘ M) ∘ d) ∘ e ∘ f
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
      a ∘ b ∘ (c ∘ M ∘ d) ∘ e ∘ f ∎

  ------------------------------------------------------------------------
  -- Shared tail-reshuffle for `box-suffix`/`box-prefix`'s `regroup-R`:
  -- `a ∘ b ∘ M ∘ c ∘ f ≈ a ∘ (b ∘ M ∘ c) ∘ f` (re-fold the raw box).
  bracket-RR
    : ∀ {O₀ O₁ O₂ O₃ O₄ O₅ : ObjTerm}
        (a : HomTerm O₄ O₅) (b : HomTerm O₃ O₄) (M : HomTerm O₂ O₃)
        (c : HomTerm O₁ O₂) (f : HomTerm O₀ O₁)
    → a ∘ b ∘ M ∘ c ∘ f
      ≈Term a ∘ (b ∘ M ∘ c) ∘ f
  bracket-RR a b M c f = begin
      a ∘ b ∘ M ∘ c ∘ f
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      a ∘ b ∘ (M ∘ c) ∘ f
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      a ∘ (b ∘ M ∘ c) ∘ f ∎

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

      -- `s-ei`/`s-eo⁻` re-expressed as `subst` over raw `HomTerm` arguments
      -- (matching `conj-lemma`'s conjugators).
      s-ei-as : subst (λ z → HomTerm z (unflatten (einL ++ (restG ++ R))))
                      (cong unflatten (sym (++-assoc einL restG R))) id
              ≡ s-ei
      s-ei-as = bridge-dom (++-assoc einL restG R)

      s-eo⁻-as : subst (λ z → HomTerm (unflatten (eoutL ++ (restG ++ R))) z)
                       (cong unflatten (sym (++-assoc eoutL restG R))) id
               ≡ s-eo⁻
      s-eo⁻-as = bridge-cod (++-assoc eoutL restG R)

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
              ≈⟨ refl⟩∘⟨ bx⊗id-expand ⟩∘⟨refl ⟩
            to-eorg-R
              ∘ ((to-eo-rg ⊗₁ id {UR})
                 ∘ ((G ⊗₁ id {Urg}) ⊗₁ id {UR})
                 ∘ (from-ei-rg ⊗₁ id {UR}))
              ∘ from-eirg-R
              ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ mid-nat ⟩∘⟨refl) ⟩∘⟨refl ⟩
            to-eorg-R
              ∘ ((to-eo-rg ⊗₁ id {UR})
                 ∘ (α⇐ {Ueo} {Urg} {UR}
                    ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                    ∘ α⇒ {Uei} {Urg} {UR})
                 ∘ (from-ei-rg ⊗₁ id {UR}))
              ∘ from-eirg-R
              ≈⟨ regroup-L ⟩
            (to-eorg-R ∘ (to-eo-rg ⊗₁ id {UR}) ∘ α⇐ {Ueo} {Urg} {UR})
              ∘ (G ⊗₁ id {Urg ⊗₀ UR})
              ∘ (α⇒ {Uei} {Urg} {UR}
                 ∘ (from-ei-rg ⊗₁ id {UR})
                 ∘ from-eirg-R)
              ≈⟨ T-eo ⟩∘⟨ refl⟩∘⟨ F-ei ⟩
            (s-eo⁻ ∘ to-eo-rgR ∘ (id {Ueo} ⊗₁ to-rgR))
              ∘ (G ⊗₁ id {Urg ⊗₀ UR})
              ∘ ((id {Uei} ⊗₁ from-rgR) ∘ from-ei-rgR ∘ s-ei)
              ≈⟨ regroup-mid ⟩
            s-eo⁻
              ∘ to-eo-rgR
              ∘ ((id {Ueo} ⊗₁ to-rgR)
                 ∘ (G ⊗₁ id {Urg ⊗₀ UR})
                 ∘ (id {Uei} ⊗₁ from-rgR))
              ∘ from-ei-rgR
              ∘ s-ei
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-collapse ⟩∘⟨refl ⟩
            s-eo⁻
              ∘ to-eo-rgR
              ∘ (G ⊗₁ id {unflatten (restG ++ R)})
              ∘ from-ei-rgR
              ∘ s-ei
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
              regroup-mid =
                bracket-mid s-eo⁻ to-eo-rgR (id {Ueo} ⊗₁ to-rgR)
                  (G ⊗₁ id {Urg ⊗₀ UR}) (id {Uei} ⊗₁ from-rgR) from-ei-rgR s-ei

              regroup-R :
                s-eo⁻
                  ∘ to-eo-rgR
                  ∘ (G ⊗₁ id {unflatten (restG ++ R)})
                  ∘ from-ei-rgR
                  ∘ s-ei
                ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
              regroup-R =
                bracket-RR s-eo⁻ to-eo-rgR (G ⊗₁ id {unflatten (restG ++ R)})
                  from-ei-rgR s-ei

  ------------------------------------------------------------------------
  -- BOX-PREFIX: mirror of `box-suffix`.  A P-prefixed box (generator acting
  -- on the right block `einR→eoutR`, preceded by an untouched left prefix
  -- `P`) running on residual `restK` factors — modulo `++-assoc` transport
  -- — as the same P-prefixed box on the EMPTY residual, tensored with `id`
  -- on `restK`.  Same proof shape as `box-suffix`, generator on the RIGHT.
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

      s-ei-as : subst (λ z → HomTerm z (unflatten (P ++ (einR ++ restK))))
                      (cong unflatten (sym (++-assoc P einR restK))) id
              ≡ s-ei
      s-ei-as = bridge-dom (++-assoc P einR restK)

      s-eo⁻-as : subst (λ z → HomTerm (unflatten (P ++ (eoutR ++ restK))) z)
                       (cong unflatten (sym (++-assoc P eoutR restK))) id
               ≡ s-eo⁻
      s-eo⁻-as = bridge-cod (++-assoc P eoutR restK)

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
              ≈⟨ refl⟩∘⟨ bx'⊗id-expand ⟩∘⟨refl ⟩
            to-Peo-rk
              ∘ ((to-P-eo ⊗₁ id {Urk})
                 ∘ ((id {UP} ⊗₁ G) ⊗₁ id {Urk})
                 ∘ (from-P-ei ⊗₁ id {Urk}))
              ∘ from-Pei-rk
              ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ mid-nat ⟩∘⟨refl) ⟩∘⟨refl ⟩
            to-Peo-rk
              ∘ ((to-P-eo ⊗₁ id {Urk})
                 ∘ (α⇐ {UP} {Ueo} {Urk}
                    ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                    ∘ α⇒ {UP} {Uei} {Urk})
                 ∘ (from-P-ei ⊗₁ id {Urk}))
              ∘ from-Pei-rk
              ≈⟨ regroup-L ⟩
            (to-Peo-rk ∘ (to-P-eo ⊗₁ id {Urk}) ∘ α⇐ {UP} {Ueo} {Urk})
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ (α⇒ {UP} {Uei} {Urk}
                 ∘ (from-P-ei ⊗₁ id {Urk})
                 ∘ from-Pei-rk)
              ≈⟨ T-eo ⟩∘⟨ refl⟩∘⟨ F-ei ⟩
            (s-eo⁻ ∘ to-P-eork ∘ (id {UP} ⊗₁ to-eo-rk))
              ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
              ∘ ((id {UP} ⊗₁ from-ei-rk) ∘ from-P-eirk ∘ s-ei)
              ≈⟨ regroup-mid ⟩
            s-eo⁻
              ∘ to-P-eork
              ∘ ((id {UP} ⊗₁ to-eo-rk)
                 ∘ (id {UP} ⊗₁ (G ⊗₁ id {Urk}))
                 ∘ (id {UP} ⊗₁ from-ei-rk))
              ∘ from-P-eirk
              ∘ s-ei
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mid-collapse ⟩∘⟨refl ⟩
            s-eo⁻
              ∘ to-P-eork
              ∘ (id {UP} ⊗₁ bx)
              ∘ from-P-eirk
              ∘ s-ei
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
              regroup-mid =
                bracket-mid s-eo⁻ to-P-eork (id {UP} ⊗₁ to-eo-rk)
                  (id {UP} ⊗₁ (G ⊗₁ id {Urk})) (id {UP} ⊗₁ from-ei-rk) from-P-eirk s-ei

              regroup-R :
                s-eo⁻
                  ∘ to-P-eork
                  ∘ (id {UP} ⊗₁ bx)
                  ∘ from-P-eirk
                  ∘ s-ei
                ≈Term s-eo⁻ ∘ bxRaw ∘ s-ei
              regroup-R =
                bracket-RR s-eo⁻ to-P-eork (id {UP} ⊗₁ bx) from-P-eirk s-ei

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
              ≈⟨ cancelˡ (_≅_.isoʳ (unflatten-++-≅ eoutR rest)) ⟩
            ((G ⊗₁ id {Ur}) ∘ from-ei-rest) ∘ to-ei-rest
              ≈⟨ cancelʳ (_≅_.isoʳ (unflatten-++-≅ einR rest)) ⟩
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
          ≈⟨ cancelˡ α⇐∘α⇒≈id ⟩
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
