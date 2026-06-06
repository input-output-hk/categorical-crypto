{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The PRUNED `⊗` shape residual `decodeP-⊗-shape`, PROVEN by mirroring
-- `Sub.DecodeTensorShape.decode-⊗-shape-inner` with the UNPRUNED decoder
-- `decode` / translation `⟪_⟫` replaced by the PRUNED `decodeP` / `⟪_⟫ₚ`:
--
--     decodeP (f ⊗₁ g)
--       ≈Term to (unflatten-++-≅ …) ∘ (decodeP f ⊗₁ decodeP g) ∘ from (…)
--
-- TENSOR IS NOT PRUNED: `⟪ f ⊗₁ g ⟫ₚ = hTensor ⟪f⟫ₚ ⟪g⟫ₚ` uses the SAME
-- `hTensor` as the unpruned side, and `decode-attempt-LinearP (f ⊗₁ g) =
-- decode-attempt-hTensor ⟪f⟫ₚ ⟪g⟫ₚ …` uses the SAME `decode-attempt-hTensor`
-- function the unpruned proof uses.  Consequently the ENTIRE tensor-block
-- machinery of `DecodeTensorShape` — `EmbedData`, `BlockFactor`,
-- `BlockTensor` — is generic in the two sub-hypergraphs and is REUSED here
-- verbatim, instantiated at `⟪f⟫ₚ` / `⟪g⟫ₚ`.  Only the top-level binding of
-- the sub-decoders (`G = ⟪f⟫ₚ`, `lin-G = ⟪⟫-LinearP f`, the
-- `decode-attempt-extract` extraction on `decode-attempt-LinearP`, and the
-- `decodeP`-folding `Gpart`/`Kpart`) differs.
--
-- This is the structural fact recorded in `ProcessEdgesTermShape`'s
-- `decodeP-⊗-shape` doc: the pruned `⊗` shape is the `decodeP` mirror of
-- `decode-⊗-shape-inner`.  Since the latter is PROVEN postulate-free over
-- `objUIP` + `K`, so is this — NO `nf-bracket` / `swap-atom-aligned` kernel
-- is consumed (the kernel is the interchange side's, not the decode-`⊗`
-- side's; the block reordering here is the proven `N`+`M` `BlockNFBraid`
-- framing inside `BlockFactor`).
--
-- Parameterised by `objUIP` + `K : FaithfulnessResidual`.  No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorPruned
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hTensor
        ; domL-hTensor; codL-hTensor
        ; map-via-inj; map-via-raise)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv

-- Pruned totality.
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP; ⟪⟫-LinearP)

-- The generic gate, the importable extraction / Unique helpers, and the
-- generic tensor-block machinery (all generic in the sub-hypergraphs).
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (pe-term-++; pe-stack-++)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using ( ≡⇒≈Term
        ; subst₂-HomTerm-irrel; subst₂-HomTerm-∘; subst₂-resp-≈Term
        ; subst₂-HomTerm-∘-dist; subst₂-⊗₁-dist
        ; permute-subst₂; map⁺-subst₂; eval-subst₂-↭
        ; vlab-φ-lemma; pvv-relabel
        ; Linear⇒cod-Unique; decode-attempt-extract )
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig
  using (module EmbedData; module BlockFactor; module BlockTensor)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData as BNB

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
open import Data.List.Properties using (map-++; map-∘; map-cong; length-map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

  -- The pruned decoder `decodeP`.
  decodeP : ∀ {A B} (f : HomTerm A B)
          → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  decodeP {A} {B} f =
    subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
           (proj₁ (decode-attempt-LinearP f))

  ------------------------------------------------------------------------
  -- subst₂ / boundary algebra: the shared lemmas now live in the leaf
  -- `HomTermTransport` (imported above); only the `unflatten-++-≅`
  -- bridges `to-uf-cong`/`from-uf-cong` remain local here.
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
-- ## The FINAL pruned ⊗ assembly — `decodeP-⊗-shape`.
--
-- Verbatim mirror of `DecodeTensorShape.decode-⊗-shape-inner`, with
-- `decode`/`decode-attempt-Linear`/`Lin.⟪⟫-Linear`/`⟪_⟫`/`⟪⟫-{dom,cod}L`
-- → `decodeP`/`decode-attempt-LinearP`/`⟪⟫-LinearP`/`⟪_⟫ₚ`/`⟪⟫ₚ-{dom,cod}L`.

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where
  open FaithfulnessResidual Kf using (permute-resp-≅↭)

  decodeP-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decodeP f ⊗₁ decodeP g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decodeP-⊗-shape {A} {B} {C₀} {D} f g = goal
    where
      G K : Hypergraph FlatGen
      G = ⟪ f ⟫ₚ
      K = ⟪ g ⟫ₚ
      module G = Hypergraph G
      module K = Hypergraph K

      Cht : Hypergraph FlatGen
      Cht = hTensor G K
      module C = Hypergraph Cht

      lin-G : Lin.Linear G
      lin-G = ⟪⟫-LinearP f
      lin-K : Lin.Linear K
      lin-K = ⟪⟫-LinearP g
      lin-C : Lin.Linear Cht
      lin-C = ⟪⟫-LinearP (f ⊗₁ g)

      open EmbedData objUIP Kf G K using (module TG; module TK)
      open BlockFactor objUIP Kf G K

      open FA.hTensor-impl G K using (injL; injR; vlab-c; vlab-injL; vlab-injR)
      open FM.HomReasoning

      ------------------------------------------------------------------
      gblk = map (_↑ˡ K.nE) (range G.nE)
      kblk = map (G.nE ↑ʳ_) (range K.nE)

      ------------------------------------------------------------------
      ext-C = decode-attempt-extract Cht
                (proj₁ (decode-attempt-LinearP (f ⊗₁ g)))
                (proj₂ (decode-attempt-LinearP (f ⊗₁ g)))
      perm-C = proj₁ ext-C
      ext-C-eq = proj₂ ext-C

      ext-f = decode-attempt-extract G
                (proj₁ (decode-attempt-LinearP f)) (proj₂ (decode-attempt-LinearP f))
      perm-f = proj₁ ext-f
      ext-f-eq = proj₂ ext-f
      ext-g = decode-attempt-extract K
                (proj₁ (decode-attempt-LinearP g)) (proj₂ (decode-attempt-LinearP g))
      perm-g = proj₁ ext-g
      ext-g-eq = proj₂ ext-g

      sG : List (Fin G.nV)
      sG = pe-stackG (range G.nE) G.dom
      sK : List (Fin K.nV)
      sK = pe-stackK (range K.nE) K.dom

      after-G : List (Fin C.nV)
      after-G = pe-stackC gblk C.dom

      after-G-≡ : after-G ≡ map injL sG ++ map injR K.dom
      after-G-≡ = mixed-stack-G (range G.nE) G.dom K.dom

      after-K : List (Fin C.nV)
      after-K = pe-stackC kblk after-G

      uCcod : Unique C.cod
      uCcod = Linear⇒cod-Unique Cht lin-C

      ------------------------------------------------------------------
      res-whole : SUR.Reservoir≤1 Cht (gblk ++ kblk) C.dom
      res-whole = SUR.dom-reservoir-prov Cht (proj₂ lin-C) (gblk ++ kblk)
                    (Perm.↭-reflexive (sym (Inv.range-++ G.nE K.nE)))

      res-G : SUR.Reservoir≤1 Cht gblk C.dom
      res-G = SUR.reservoir-prefix Cht gblk kblk C.dom res-whole

      res-K-aG : SUR.Reservoir≤1 Cht kblk after-G
      res-K-aG = SUR.reservoir-split Cht gblk kblk C.dom res-whole

      res-K : SUR.Reservoir≤1 Cht kblk (map injL sG ++ map injR K.dom)
      res-K = subst (SUR.Reservoir≤1 Cht kblk) after-G-≡ res-K-aG

      ------------------------------------------------------------------
      decode-f-≈
        : decodeP f ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
            (permute-via-vlab G.vlab perm-f ∘ proj₂ (process-edges G (range G.nE) G.dom))
      decode-f-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f))
                                       (cong unflatten (⟪⟫ₚ-codL f)))
                      ext-f-eq)

      decode-g-≈
        : decodeP g ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL g)) (cong unflatten (⟪⟫ₚ-codL g))
            (permute-via-vlab K.vlab perm-g ∘ proj₂ (process-edges K (range K.nE) K.dom))
      decode-g-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL g))
                                       (cong unflatten (⟪⟫ₚ-codL g)))
                      ext-g-eq)

      decode-fg-≈
        : decodeP (f ⊗₁ g) ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL (f ⊗₁ g)))
                         (cong unflatten (⟪⟫ₚ-codL (f ⊗₁ g)))
            (permute-via-vlab C.vlab perm-C
             ∘ proj₂ (process-edges Cht (range C.nE) C.dom))
      decode-fg-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL (f ⊗₁ g)))
                                       (cong unflatten (⟪⟫ₚ-codL (f ⊗₁ g))))
                      ext-C-eq)

      ----------------------------------------------------------------
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
      KBr = KBraid (range K.nE) sG K.dom
      KCl = KClean (range K.nE) sG K.dom

      combP : (map injL sG ++ map injR sK) Perm.↭ C.cod
      combP = Perm.↭-trans (Perm.↭-sym KBr) perm-C2-cl

      pfL : map injL sG Perm.↭ map injL G.cod
      pfL = PermProp.map⁺ injL perm-f
      pfR : map injR sK Perm.↭ map injR K.cod
      pfR = PermProp.map⁺ injR perm-g

      combP-coh : pvlC combP ≈Term pvlC (PermProp.++⁺ pfL pfR)
      combP-coh = pvlC-coh uCcod combP (PermProp.++⁺ pfL pfR)

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
      Pcomp-eq : PC ∘ Pcomposite ≈Term to-cod ∘ (Gᶜ ⊗₁ Kᶜ) ∘ from-dom
      Pcomp-eq =
        ≈-Term-trans step1
          (≈-Term-trans step2
            (≈-Term-trans step3
              (≈-Term-trans step4 collapse)))

      ----------------------------------------------------------------
      eAdom : map C.vlab (map injL G.dom) ≡ flatten A
      eAdom = trans (TG.vlab-φ G.dom) (⟪⟫ₚ-domL f)
      eCdom : map C.vlab (map injR K.dom) ≡ flatten C₀
      eCdom = trans (TK.vlab-φ K.dom) (⟪⟫ₚ-domL g)
      eBcod : map C.vlab (map injL G.cod) ≡ flatten B
      eBcod = trans (TG.vlab-φ G.cod) (⟪⟫ₚ-codL f)
      eDcod : map C.vlab (map injR K.cod) ≡ flatten D
      eDcod = trans (TK.vlab-φ K.cod) (⟪⟫ₚ-codL g)

      domFG = cong unflatten (⟪⟫ₚ-domL (f ⊗₁ g))
      codFG = cong unflatten (⟪⟫ₚ-codL (f ⊗₁ g))

      midⱽ = cong₂ _⊗₀_ (cong unflatten eBcod) (cong unflatten eDcod)
      midᵂ = cong₂ _⊗₀_ (cong unflatten eAdom) (cong unflatten eCdom)

      ----------------------------------------------------------------
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
      PF = permute-via-vlab G.vlab perm-f
      PG = permute-via-vlab K.vlab perm-g

      coeC-is-subst₂
        : ∀ {d s s' : List (Fin C.nV)} (eq : s ≡ s')
            (t : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s)))
        → coeC {d} eq t
          ≡ subst₂ HomTerm refl (cong unflatten (cong (map C.vlab) eq)) t
      coeC-is-subst₂ refl t = refl

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

      Gpart : subst₂ HomTerm (cong unflatten eAdom) (cong unflatten eBcod) Gᶜ ≈Term decodeP f
      Gpart =
        ≈-Term-trans
          (subst₂-HomTerm-irrel objUIP
            (cong unflatten eAdom)
            (trans (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (⟪⟫ₚ-domL f)))
            (cong unflatten eBcod)
            (trans (cong unflatten (TG.vlab-φ G.cod)) (cong unflatten (⟪⟫ₚ-codL f)))
            Gᶜ)
        (≈-Term-trans
          (≡⇒≈Term (sym (subst₂-HomTerm-∘
                          (cong unflatten (TG.vlab-φ G.dom)) (cong unflatten (⟪⟫ₚ-domL f))
                          (cong unflatten (TG.vlab-φ G.cod)) (cong unflatten (⟪⟫ₚ-codL f))
                          Gᶜ)))
        (≈-Term-trans
          (subst₂-resp-≈Term (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f)) Gᶜ-twin)
          (≈-Term-sym decode-f-≈)))

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

      Kpart : subst₂ HomTerm (cong unflatten eCdom) (cong unflatten eDcod) Kᶜ ≈Term decodeP g
      Kpart =
        ≈-Term-trans
          (subst₂-HomTerm-irrel objUIP
            (cong unflatten eCdom)
            (trans (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (⟪⟫ₚ-domL g)))
            (cong unflatten eDcod)
            (trans (cong unflatten (TK.vlab-φ K.cod)) (cong unflatten (⟪⟫ₚ-codL g)))
            Kᶜ)
        (≈-Term-trans
          (≡⇒≈Term (sym (subst₂-HomTerm-∘
                          (cong unflatten (TK.vlab-φ K.dom)) (cong unflatten (⟪⟫ₚ-domL g))
                          (cong unflatten (TK.vlab-φ K.cod)) (cong unflatten (⟪⟫ₚ-codL g))
                          Kᶜ)))
        (≈-Term-trans
          (subst₂-resp-≈Term (cong unflatten (⟪⟫ₚ-domL g)) (cong unflatten (⟪⟫ₚ-codL g)) Kᶜ-twin)
          (≈-Term-sym decode-g-≈)))

      ----------------------------------------------------------------
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
        : subst₂ HomTerm midᵂ midⱽ (Gᶜ ⊗₁ Kᶜ) ≈Term decodeP f ⊗₁ decodeP g
      mid-fold =
        ≈-Term-trans
          (≡⇒≈Term (subst₂-⊗₁-dist
                      (cong unflatten eAdom) (cong unflatten eBcod)
                      (cong unflatten eCdom) (cong unflatten eDcod) Gᶜ Kᶜ))
          (⊗-resp-≈ Gpart Kpart)

      goal : decodeP (f ⊗₁ g)
           ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                ∘ (decodeP f ⊗₁ decodeP g)
                ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C₀))
      goal =
        ≈-Term-trans decode-fg-≈
        (≈-Term-trans
          (subst₂-resp-≈Term domFG codFG Pcomp-eq)
        (≈-Term-trans
          (≡⇒≈Term dist)
          (∘-resp-≈ (≡⇒≈Term to-glue)
            (∘-resp-≈ mid-fold (≡⇒≈Term from-glue)))))
