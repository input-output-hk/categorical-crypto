{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The UNPRUNED `∘` shape residual `decode-∘-shape-inner`, PROVEN by
-- ASSEMBLING three already-proven tools (NO new postulate):
--
--   1. `StackEquivariance.process-edges-equivariant`  — input-permutation
--      bridge for the K-block (its start stack `map injL s_G_final` is only
--      `↭` to the canonical `map injL G.cod = map remap K.dom`).
--   2. `ProcessEdgesTermShape.TermEmbed.process-edges-term-emb-gen` — relabel
--      the CANONICAL G/K block runs into the sub-decoder process-terms
--      (φ = injL / remap, ψ = _↑ˡ K.nE / G.nE ↑ʳ_).
--   3. `PermuteCoherenceK.permute-via-vlab-≈Term-coherence-K` — collapse the
--      composite's `final-permute` against the per-side ones + the residual
--      permutes from steps 1–2 (codomain `Unique` from `⟪⟫-cod-unique`).
--
-- glued with `ProcessEdgesTermShape.pe-term-++` over `Invariant.range-++`.
--
-- Parameterised by `objUIP` (UIP on `ObjTerm`) and `K : FaithfulnessResidual`
-- — the same two K-inputs the rest of the completeness chain threads
-- (`DecodeRelRespIsoWired` supplies them at the consume site).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposeShape
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hCompose
        ; domL-hCompose; codL-hCompose
        ; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL; map-via-inj; map-via-raise)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; process-all-edges
        ; decode-attempt; Agen-edge; extract-exact; ++-[]-↭)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; decode-attempt-Linear; process-edges-++-stack
        ; process-edges-↑ˡ-pure-L)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (module TermEmbed; pe-term-++; pe-stack-++; module Assemble)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance sig as SE
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.Hypergraph.ExtractPrefixEvalPhi
  using (eval-map⁺; cast-irrel; subst₂-FinBij-∘; ≈-fb-of-≡)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (↑ˡ-injective)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++; map-∘; map-cong; length-map)
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

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using ( ≡⇒≈Term
        ; subst₂-FlatGen-cancel; subst₂-FlatGen-cancel′
        ; subst₂-HomTerm-irrel; subst₂-HomTerm-∘; subst₂-resp-≈Term
        ; subst₂-HomTerm-∘-dist; permute-subst₂; map⁺-subst₂
        ; eval-subst₂-↭; vlab-φ-lemma; pvv-relabel
        ; Linear⇒cod-Unique; decode-attempt-extract )

--------------------------------------------------------------------------------
-- ## Embedding data for `hCompose ⟪f⟫ ⟪g⟫`.
--
-- For fixed `G K bdy`, the composite `C = hCompose G K bdy` admits two
-- injective, label-preserving embeddings of the SUB-hypergraphs:
--
--   * G-side : φ = injL,  ψ = _↑ˡ K.nE   (the `eG ↑ˡ K.nE` edges).
--   * K-side : φ = remap, ψ = G.nE ↑ʳ_   (the `G.nE ↑ʳ eK` edges).
--
-- We package each as the `TermEmbed` parameters via the FromAPROP
-- reduction lemmas, so `process-edges-term-emb-gen` applies.

module EmbedData
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  (G K : Hypergraph FlatGen) (bdy : codL G ≡ domL K)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hCompose G K bdy)
  open FA.hCompose-impl G K bdy

  C-hg : Hypergraph FlatGen
  C-hg = hCompose G K bdy

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

  module TG = TermEmbed {H = G} {J = hCompose G K bdy} objUIP Kf
                injL (↑ˡ-injective K.nV _ _)
                vlab-injL
                ψG ein-c-inj₁-red eout-c-inj₁-red
                atom-einG atom-eoutG ψ-elabG

  ------------------------------------------------------------------------
  -- K-side embedding: φ = remap, ψ = G.nE ↑ʳ_, H = K, J = C.
  -- `remap` injectivity comes from `Linear G + Linear K` (the sig-level
  -- `Linearity.hCompose-Linear-utils.remap-injective`).
  ------------------------------------------------------------------------

  module _ (lin-G : Lin.Linear G) (lin-K : Lin.Linear K) where
    open Lin.hCompose-Linear-utils G K bdy lin-G lin-K using (remap-injective)

    ψK : Fin K.nE → Fin C.nE
    ψK eK = G.nE ↑ʳ eK

    atom-einK : ∀ eK → map C.vlab (C.ein (ψK eK)) ≡ map K.vlab (K.ein eK)
    atom-einK eK = trans (cong (map vlab-c) (ein-c-inj₂-red eK))
                         (sym (map-via-remap (K.ein eK)))

    atom-eoutK : ∀ eK → map C.vlab (C.eout (ψK eK)) ≡ map K.vlab (K.eout eK)
    atom-eoutK eK = trans (cong (map vlab-c) (eout-c-inj₂-red eK))
                          (sym (map-via-remap (K.eout eK)))

    ψ-elabK : ∀ eK → subst₂ FlatGen (atom-einK eK) (atom-eoutK eK) (C.elab (ψK eK))
                   ≡ K.elab eK
    ψ-elabK eK =
      trans (subst₂-FlatGen-cancel
               (cong (map vlab-c) (ein-c-inj₂-red eK))
               (cong (map vlab-c) (eout-c-inj₂-red eK))
               (map-via-remap (K.ein eK))
               (map-via-remap (K.eout eK))
               (elab-c (G.nE ↑ʳ eK)))
            (trans (cong (subst₂ FlatGen
                            (sym (map-via-remap (K.ein eK)))
                            (sym (map-via-remap (K.eout eK))))
                         (elab-c-inj₂ eK))
                   (subst₂-FlatGen-cancel′
                      (map-via-remap (K.ein eK))
                      (map-via-remap (K.eout eK))
                      (K.elab eK)))

    module TK = TermEmbed {H = K} {J = hCompose G K bdy} objUIP Kf
                  remap remap-injective
                  remap-vlab
                  ψK ein-c-inj₂-red eout-c-inj₂-red
                  atom-einK atom-eoutK ψ-elabK

--------------------------------------------------------------------------------
-- ## `Linear H ⇒ Unique (cod H)` + algorithm extraction (sig-level).
--
-- `Linear⇒cod-Unique` and `decode-attempt-extract` now live in the shared
-- leaf `HomTermTransport` (imported at the top of this module).

--------------------------------------------------------------------------------
-- ## The main assembly.

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where
  open FaithfulnessResidual Kf using (permute-resp-≅↭)

  decode-∘-shape-inner
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode (g ∘ f) ≈Term decode g ∘ decode f
  decode-∘-shape-inner {A} {B} {C₀} g f = goal
    where
      G K : Hypergraph FlatGen
      G = ⟪ f ⟫
      K = ⟪ g ⟫
      module G = Hypergraph G
      module K = Hypergraph K

      bdy : codL G ≡ domL K
      bdy = trans (⟪⟫-codL f) (sym (⟪⟫-domL g))

      Chg : Hypergraph FlatGen
      Chg = hCompose G K bdy
      module C = Hypergraph Chg

      lin-G : Lin.Linear G
      lin-G = Lin.⟪⟫-Linear f
      lin-K : Lin.Linear K
      lin-K = Lin.⟪⟫-Linear g

      open EmbedData objUIP Kf G K bdy
      module TKm = TK lin-G lin-K
      open FA.hCompose-impl G K bdy using (injL; remap; map-via-remap; vlab-injL; remap-vlab)
      open Lin.hCompose-Linear-utils G K bdy lin-G lin-K using (map-remap-K-dom)

      -- pe-term / pe-stack abbreviations on each hypergraph.
      pe-stack : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nE H))
               → List (Fin (Hypergraph.nV H)) → List (Fin (Hypergraph.nV H))
      pe-stack H o s = proj₁ (process-edges H o s)

      -- The composite's whole-run inner term, extracted with its perm.
      ext-C = decode-attempt-extract Chg
                (proj₁ (decode-attempt-Linear (g ∘ f)))
                (proj₂ (decode-attempt-Linear (g ∘ f)))
      perm-C = proj₁ ext-C
      ext-C-eq = proj₂ ext-C

      -- The two sub-decoders, extracted.
      ext-f = decode-attempt-extract G
                (proj₁ (decode-attempt-Linear f)) (proj₂ (decode-attempt-Linear f))
      perm-f = proj₁ ext-f
      ext-f-eq = proj₂ ext-f
      ext-g = decode-attempt-extract K
                (proj₁ (decode-attempt-Linear g)) (proj₂ (decode-attempt-Linear g))
      perm-g = proj₁ ext-g
      ext-g-eq = proj₂ ext-g

      -- Edge blocks.
      gblk = map (_↑ˡ K.nE) (range G.nE)
      kblk = map (G.nE ↑ʳ_) (range K.nE)

      -- C.dom = map injL G.dom (definitional).
      after-G : List (Fin C.nV)
      after-G = pe-stack Chg gblk C.dom

      ----------------------------------------------------------------
      -- The G-block term-twin (φ = injL).  `map ψG (range G.nE) = gblk`
      -- and `map injL G.dom = C.dom`, both definitional.
      G-block-twin
        : subst₂ HomTerm
            (cong unflatten (TG.vlab-φ G.dom))
            (cong unflatten
              (trans (cong (map C.vlab) (TG.proc-stack-emb (range G.nE) G.dom))
                     (TG.vlab-φ (pe-stack G (range G.nE) G.dom))))
            (proj₂ (process-edges Chg gblk C.dom))
          ≈Term proj₂ (process-edges G (range G.nE) G.dom)
      G-block-twin = TG.process-edges-term-emb (range G.nE) G.dom

      -- The G-decoder's final stack (= `pe-stack G (range G.nE) G.dom`).
      s_G_final : List (Fin G.nV)
      s_G_final = pe-stack G (range G.nE) G.dom

      -- `after-G ≡ map injL s_G_final` (G-edges leave a pure-L stack).
      after-G-≡ : after-G ≡ map injL s_G_final
      after-G-≡ = cong proj₁ (proj₂ (process-edges-↑ˡ-pure-L G K bdy lin-G lin-K
                                       (range G.nE) G.dom))

      -- `after-G ↭ map remap K.dom` (the canonical K-input).
      after-G-↭ : after-G Perm.↭ map remap K.dom
      after-G-↭ =
        Perm.↭-trans (Perm.↭-reflexive after-G-≡)
          (Perm.↭-trans (PermProp.map⁺ injL perm-f)
                        (Perm.↭-reflexive (sym map-remap-K-dom)))

      ----------------------------------------------------------------
      -- Reservoir for the K-block, from `Linear Chg` (= ⟪g∘f⟫-Linear).
      -- `Linear Chg = ⟪⟫-Linear (g ∘ f)` since `⟪ g ∘ f ⟫ = Chg`.
      lin-C : Lin.Linear Chg
      lin-C = Lin.⟪⟫-Linear (g ∘ f)

      reservoir-K : SUR.Reservoir≤1 Chg kblk after-G
      reservoir-K =
        SUR.reservoir-split Chg gblk kblk C.dom
          (SUR.dom-reservoir-prov Chg (proj₂ lin-C) (gblk ++ kblk)
            (Perm.↭-reflexive (sym (Inv.range-++ G.nE K.nE))))

      -- Equivariance: rewrite the K-block run-from-`after-G` into the
      -- canonical run-from-`map remap K.dom`, conjugated by permutes.
      equiv-K = SE.process-edges-equivariant Chg Kf kblk
                  after-G-↭ reservoir-K
      ρf-K = proj₁ equiv-K
      equiv-K-eq = proj₂ equiv-K

      ----------------------------------------------------------------
      -- The K-block term-twin (φ = remap), on the CANONICAL start
      -- stack `map remap K.dom = map φK K.dom` and `kblk = map ψK …`.
      K-block-twin
        : subst₂ HomTerm
            (cong unflatten (TKm.vlab-φ K.dom))
            (cong unflatten
              (trans (cong (map C.vlab) (TKm.proc-stack-emb (range K.nE) K.dom))
                     (TKm.vlab-φ (pe-stack K (range K.nE) K.dom))))
            (proj₂ (process-edges Chg kblk (map remap K.dom)))
          ≈Term proj₂ (process-edges K (range K.nE) K.dom)
      K-block-twin = TKm.process-edges-term-emb (range K.nE) K.dom

      ----------------------------------------------------------------
      -- Run-split: the composite process-term factors into the K-block
      -- term ∘ G-block term (the edge list `range C.nE` splits as
      -- `gblk ++ kblk` by `Inv.range-++`, then `pe-term-++`).
      --
      -- `process-edges Chg (range C.nE) C.dom` and
      -- `process-edges Chg (gblk ++ kblk) C.dom` agree after rewriting the
      -- edge list along `Inv.range-++ G.nE K.nE`.
      -- Codomain transport along a C-stack equality.
      coeC : ∀ {s s' : List (Fin C.nV)} → s ≡ s'
           → HomTerm (unflatten (map C.vlab C.dom)) (unflatten (map C.vlab s))
           → HomTerm (unflatten (map C.vlab C.dom)) (unflatten (map C.vlab s'))
      coeC eq = subst (λ z → HomTerm (unflatten (map C.vlab C.dom))
                                      (unflatten (map C.vlab z))) eq

      -- The edge-list rewrite, as a transported equality of `process-edges`
      -- (dependent in the final stack).
      run-split-term
        : proj₂ (process-edges Chg (range C.nE) C.dom)
          ≈Term coeC (sym (cong (λ es → pe-stack Chg es C.dom)
                                (Inv.range-++ G.nE K.nE)))
                     (proj₂ (process-edges Chg (gblk ++ kblk) C.dom))
      run-split-term =
        elim (Inv.range-++ G.nE K.nE)
        where
          -- generalise the edge list, then match the rewrite at refl.
          elim : ∀ {es : List (Fin C.nE)} (eq : range C.nE ≡ es)
               → proj₂ (process-edges Chg (range C.nE) C.dom)
                 ≈Term coeC (sym (cong (λ es' → pe-stack Chg es' C.dom) eq))
                            (proj₂ (process-edges Chg es C.dom))
          elim refl = ≈-Term-refl

      -- The `pe-term-++` block factorization (the generic lemma at Chg).
      block-fact = pe-term-++ Chg gblk kblk C.dom

      ----------------------------------------------------------------
      -- Expose `decode` of each term as the subst₂-transport of its
      -- extracted inner form.
      decode-f-≈
        : decode f ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
            (permute-via-vlab G.vlab perm-f ∘ proj₂ (process-edges G (range G.nE) G.dom))
      decode-f-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫-domL f))
                                       (cong unflatten (⟪⟫-codL f)))
                      ext-f-eq)

      decode-g-≈
        : decode g ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫-domL g)) (cong unflatten (⟪⟫-codL g))
            (permute-via-vlab K.vlab perm-g ∘ proj₂ (process-edges K (range K.nE) K.dom))
      decode-g-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫-domL g))
                                       (cong unflatten (⟪⟫-codL g)))
                      ext-g-eq)

      decode-gf-≈
        : decode (g ∘ f) ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫-domL (g ∘ f)))
                         (cong unflatten (⟪⟫-codL (g ∘ f)))
            (permute-via-vlab C.vlab perm-C
             ∘ proj₂ (process-edges Chg (range C.nE) C.dom))
      decode-gf-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫-domL (g ∘ f)))
                                       (cong unflatten (⟪⟫-codL (g ∘ f))))
                      ext-C-eq)

      ----------------------------------------------------------------
      -- The codomain `Unique`s (from `Linear` of each hypergraph).
      uGcod : Unique G.cod
      uGcod = Linear⇒cod-Unique G lin-G
      uKcod : Unique K.cod
      uKcod = Linear⇒cod-Unique K lin-K
      uCcod : Unique C.cod
      uCcod = Linear⇒cod-Unique Chg lin-C

      -- The C-level final-permute keystone collapse: any two `↭ C.cod`.
      permC-coh
        : ∀ {s : List (Fin C.nV)} (p q : s Perm.↭ C.cod)
        → permute-via-vlab C.vlab p ≈Term permute-via-vlab C.vlab q
      permC-coh p q = permute-via-vlab-≈Term-coherence-K Kf C.vlab uCcod p q

      -- abbreviations for the inner terms.
      gterm = proj₂ (process-edges Chg gblk C.dom)
      kterm-canon = proj₂ (process-edges Chg kblk (map remap K.dom))
      pterm-f = proj₂ (process-edges G (range G.nE) G.dom)
      pterm-g = proj₂ (process-edges K (range K.nE) K.dom)

      ----------------------------------------------------------------
      -- Convenient names for the C-coordinate boundary objects.
      PC = permute-via-vlab C.vlab perm-C
      Pcomposite = proj₂ (process-edges Chg (range C.nE) C.dom)

      -- The K-block run-from-`after-G` term (the SE statement's LHS).
      kterm-aG = proj₂ (process-edges Chg kblk after-G)

      ----------------------------------------------------------------
      -- `Unique (map remap K.dom)` (= `map injL G.cod`), for the
      -- intermediate keystone collapse at the G/K boundary.
      uRemapKdom : Unique (map remap K.dom)
      uRemapKdom =
        subst Unique (sym map-remap-K-dom)
          (UniqueProp.map⁺ (λ {x} {y} → ↑ˡ-injective K.nV x y) uGcod)

      -- Keystone collapse at codomain `map remap K.dom`.
      permRemap-coh
        : ∀ {s : List (Fin C.nV)} (p q : s Perm.↭ map remap K.dom)
        → permute-via-vlab C.vlab p ≈Term permute-via-vlab C.vlab q
      permRemap-coh p q =
        permute-via-vlab-≈Term-coherence-K Kf C.vlab uRemapKdom p q

      ----------------------------------------------------------------
      -- Absorb a codomain `subst`-transport (the `coeC`/`coe-cod` of the
      -- run-split / block factoring) into the precomposed `permute`'s
      -- source: `permute-via-vlab C.vlab perm ∘ coe eq t`
      --   ≈ permute-via-vlab C.vlab (re-based perm) ∘ t`.  (`eq := refl`.)
      Cdom-obj = unflatten (map C.vlab C.dom)

      absorb-coe
        : ∀ {ys} {s s' : List (Fin C.nV)} (eq : s ≡ s')
            (perm : s' Perm.↭ ys)
            (t : HomTerm Cdom-obj (unflatten (map C.vlab s)))
        → permute-via-vlab C.vlab perm
            ∘ subst (λ z → HomTerm Cdom-obj (unflatten (map C.vlab z))) eq t
          ≈Term permute-via-vlab C.vlab (subst (λ z → z Perm.↭ ys) (sym eq) perm) ∘ t
      absorb-coe refl perm t = ≈-Term-refl

      -- Step 1: run-split + absorb the `coeC` into PC.
      eqRS = sym (cong (λ es → pe-stack Chg es C.dom) (Inv.range-++ G.nE K.nE))
      perm-C1 = subst (λ z → z Perm.↭ C.cod) (sym eqRS) perm-C

      step1 : PC ∘ Pcomposite
            ≈Term permute-via-vlab C.vlab perm-C1
                    ∘ proj₂ (process-edges Chg (gblk ++ kblk) C.dom)
      step1 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl run-split-term)
                           (absorb-coe eqRS perm-C
                              (proj₂ (process-edges Chg (gblk ++ kblk) C.dom)))

      -- Step 2: block-fact + absorb the `coe-cod` into perm-C1.
      eqBF = sym (pe-stack-++ Chg gblk kblk C.dom)
      perm-C2 = subst (λ z → z Perm.↭ C.cod) (sym eqBF) perm-C1

      step2 : permute-via-vlab C.vlab perm-C1
                ∘ proj₂ (process-edges Chg (gblk ++ kblk) C.dom)
            ≈Term permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
      step2 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl block-fact)
                           (absorb-coe eqBF perm-C1 (kterm-aG ∘ gterm))

      -- Step 3: equiv-K on the K-block run-from-after-G.
      step3 : permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
            ≈Term permute-via-vlab C.vlab perm-C2
                    ∘ ((permute-via-vlab C.vlab (Perm.↭-sym ρf-K)
                        ∘ (kterm-canon ∘ permute-via-vlab C.vlab after-G-↭))
                       ∘ gterm)
      step3 = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ equiv-K-eq ≈-Term-refl)

      -- Step 4: re-associate into `Xc ∘ Yc`, with
      --   Yc = pvv after-G-↭ ∘ gterm,
      --   Xc = pvv perm-C2 ∘ (pvv (↭-sym ρf-K) ∘ kterm-canon).
      reassoc
        : ∀ {O1 O2 O2' O3 O4 O5}
            (A : HomTerm O4 O5) (B : HomTerm O3 O4) (Kt : HomTerm O2' O3)
            (Ct : HomTerm O2 O2') (Gt : HomTerm O1 O2)
        → A ∘ ((B ∘ (Kt ∘ Ct)) ∘ Gt)
          ≈Term (A ∘ (B ∘ Kt)) ∘ (Ct ∘ Gt)
      reassoc A B Kt Ct Gt =
        ≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc))
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                      (≈-Term-sym assoc)))

      Yc = permute-via-vlab C.vlab after-G-↭ ∘ gterm
      Xc = permute-via-vlab C.vlab perm-C2
             ∘ (permute-via-vlab C.vlab (Perm.↭-sym ρf-K) ∘ kterm-canon)

      step4 : permute-via-vlab C.vlab perm-C2
                ∘ ((permute-via-vlab C.vlab (Perm.↭-sym ρf-K)
                    ∘ (kterm-canon ∘ permute-via-vlab C.vlab after-G-↭))
                   ∘ gterm)
            ≈Term Xc ∘ Yc
      step4 = reassoc (permute-via-vlab C.vlab perm-C2)
                      (permute-via-vlab C.vlab (Perm.↭-sym ρf-K))
                      kterm-canon
                      (permute-via-vlab C.vlab after-G-↭)
                      gterm

      -- The outer boundary transports (from `decode-gf-≈`).
      domGF = cong unflatten (⟪⟫-domL (g ∘ f))
      codGF = cong unflatten (⟪⟫-codL (g ∘ f))

      -- Middle boundary proof: `map C.vlab (map remap K.dom) ≡ flatten B`.
      midList : map C.vlab (map remap K.dom) ≡ flatten B
      midList = trans (cong (map C.vlab) map-remap-K-dom)
                      (trans (TG.vlab-φ G.cod) (⟪⟫-codL f))
      midGF = cong unflatten midList

      -- Step 5: distribute the outer subst₂ over the `Xc ∘ Yc` split.
      step5 : subst₂ HomTerm domGF codGF (Xc ∘ Yc)
            ≡ subst₂ HomTerm midGF codGF Xc ∘ subst₂ HomTerm domGF midGF Yc
      step5 = subst₂-HomTerm-∘-dist domGF midGF codGF Xc Yc

      ----------------------------------------------------------------
      -- The G-block twin codomain proof (`map C.vlab after-G ≡
      -- map G.vlab s_G_final`).
      M1 = cong unflatten
             (trans (cong (map C.vlab) (TG.proc-stack-emb (range G.nE) G.dom))
                    (TG.vlab-φ s_G_final))

      gtwin' : subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom)) M1 gterm
             ≈Term pterm-f
      gtwin' = G-block-twin

      ----------------------------------------------------------------
      -- The G-block permute reconciliation.
      midG-cod : map C.vlab (map remap K.dom) ≡ map G.vlab G.cod
      midG-cod = trans (cong (map C.vlab) map-remap-K-dom) (TG.vlab-φ G.cod)

      -- The relabel of `perm-f` viewed at C-level (source `after-G`, cod
      -- `map remap K.dom`), via the two stack equalities.
      injf-↭ : after-G Perm.↭ map remap K.dom
      injf-↭ = subst₂ Perm._↭_ (sym after-G-≡) (sym map-remap-K-dom)
                 (PermProp.map⁺ injL perm-f)

      -- `pvv C.vlab injf-↭` re-expressed as a `subst₂` of the clean relabel
      -- `pvv C.vlab (map⁺ injL perm-f)`.
      injf-↭-pvv
        : permute-via-vlab C.vlab injf-↭
          ≡ subst₂ HomTerm
              (cong unflatten (cong (map C.vlab) (sym after-G-≡)))
              (cong unflatten (cong (map C.vlab) (sym map-remap-K-dom)))
              (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f))
      injf-↭-pvv =
        trans (cong permute (map⁺-subst₂ C.vlab (sym after-G-≡) (sym map-remap-K-dom)
                               (PermProp.map⁺ injL perm-f)))
              (sym (permute-subst₂ (cong (map C.vlab) (sym after-G-≡))
                                   (cong (map C.vlab) (sym map-remap-K-dom))
                                   (PermProp.map⁺ C.vlab (PermProp.map⁺ injL perm-f))))

      PF = permute-via-vlab G.vlab perm-f

      gperm'
        : subst₂ HomTerm M1 (cong unflatten midG-cod)
            (permute-via-vlab C.vlab after-G-↭)
          ≈Term PF
      gperm' =
        ≈-Term-trans
          (subst₂-resp-≈Term M1 (cong unflatten midG-cod)
            (permRemap-coh after-G-↭ injf-↭))
        (≈-Term-trans
          (≡⇒≈Term (cong (subst₂ HomTerm M1 (cong unflatten midG-cod)) injf-↭-pvv))
        (≈-Term-trans
          (≡⇒≈Term (subst₂-HomTerm-∘
                      (cong unflatten (cong (map C.vlab) (sym after-G-≡))) M1
                      (cong unflatten (cong (map C.vlab) (sym map-remap-K-dom)))
                      (cong unflatten midG-cod)
                      (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f))))
        (≈-Term-trans
          (subst₂-HomTerm-irrel objUIP _
            (cong unflatten (vlab-φ-lemma injL C.vlab G.vlab vlab-injL s_G_final))
            _ (cong unflatten (vlab-φ-lemma injL C.vlab G.vlab vlab-injL G.cod))
            (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f)))
          (pvv-relabel Kf injL C.vlab G.vlab vlab-injL perm-f))))

      -- The G-block twin: `Yc` (C-level) transports to `PF ∘ pterm-f`.
      Yc-twin
        : subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom))
                          (cong unflatten midG-cod) Yc
          ≈Term PF ∘ pterm-f
      Yc-twin =
        ≈-Term-trans
          (≡⇒≈Term
            (subst₂-HomTerm-∘-dist (cong unflatten (TG.vlab-φ G.dom)) M1
              (cong unflatten midG-cod)
              (permute-via-vlab C.vlab after-G-↭) gterm))
          (∘-resp-≈ gperm' gtwin')

      domF = cong unflatten (⟪⟫-domL f)
      codF = cong unflatten (⟪⟫-codL f)

      Gpart : subst₂ HomTerm domGF midGF Yc ≈Term decode f
      Gpart =
        ≈-Term-trans
          (subst₂-HomTerm-irrel objUIP domGF
            (trans (cong unflatten (TG.vlab-φ G.dom)) domF)
            midGF (trans (cong unflatten midG-cod) codF) Yc)
        (≈-Term-trans
          (≡⇒≈Term (sym (subst₂-HomTerm-∘
                          (cong unflatten (TG.vlab-φ G.dom)) domF
                          (cong unflatten midG-cod) codF Yc)))
        (≈-Term-trans
          (subst₂-resp-≈Term domF codF Yc-twin)
          (≈-Term-sym decode-f-≈)))

      ----------------------------------------------------------------
      -- ### The K-block.
      combP : pe-stack Chg kblk (map remap K.dom) Perm.↭ C.cod
      combP = Perm.trans (Perm.↭-sym ρf-K) perm-C2

      -- `Xc ≈ pvv combP ∘ kterm-canon` (assoc + the definitional pvv-trans).
      Xc-assoc : Xc ≈Term permute-via-vlab C.vlab combP ∘ kterm-canon
      Xc-assoc = ≈-Term-sym assoc

      -- K-block twin codomain proof.
      MK1 = cong unflatten
              (trans (cong (map C.vlab) (TKm.proc-stack-emb (range K.nE) K.dom))
                     (TKm.vlab-φ (pe-stack K (range K.nE) K.dom)))

      ktwin' : subst₂ HomTerm (cong unflatten (TKm.vlab-φ K.dom)) MK1 kterm-canon
             ≈Term pterm-g
      ktwin' = K-block-twin

      -- The K-block permute reconciliation.
      PG = permute-via-vlab K.vlab perm-g

      proc-stack-emb-K
        : pe-stack Chg kblk (map remap K.dom)
          ≡ map remap (pe-stack K (range K.nE) K.dom)
      proc-stack-emb-K = TKm.proc-stack-emb (range K.nE) K.dom

      remapg-↭ : pe-stack Chg kblk (map remap K.dom) Perm.↭ C.cod
      remapg-↭ = subst₂ Perm._↭_ (sym proc-stack-emb-K) refl
                   (PermProp.map⁺ remap perm-g)

      remapg-↭-pvv
        : permute-via-vlab C.vlab remapg-↭
          ≡ subst₂ HomTerm
              (cong unflatten (cong (map C.vlab) (sym proc-stack-emb-K)))
              (cong unflatten (cong (map C.vlab) refl))
              (permute-via-vlab C.vlab (PermProp.map⁺ remap perm-g))
      remapg-↭-pvv =
        trans (cong permute (map⁺-subst₂ C.vlab (sym proc-stack-emb-K) refl
                               (PermProp.map⁺ remap perm-g)))
              (sym (permute-subst₂ (cong (map C.vlab) (sym proc-stack-emb-K))
                                   (cong (map C.vlab) refl)
                                   (PermProp.map⁺ C.vlab (PermProp.map⁺ remap perm-g))))

      kperm'
        : subst₂ HomTerm MK1 (cong unflatten (TKm.vlab-φ K.cod))
            (permute-via-vlab C.vlab combP)
          ≈Term PG
      kperm' =
        ≈-Term-trans
          (subst₂-resp-≈Term MK1 (cong unflatten (TKm.vlab-φ K.cod))
            (permC-coh combP remapg-↭))
        (≈-Term-trans
          (≡⇒≈Term (cong (subst₂ HomTerm MK1 (cong unflatten (TKm.vlab-φ K.cod)))
                         remapg-↭-pvv))
        (≈-Term-trans
          (≡⇒≈Term (subst₂-HomTerm-∘
                      (cong unflatten (cong (map C.vlab) (sym proc-stack-emb-K))) MK1
                      (cong unflatten (cong (map C.vlab) refl))
                      (cong unflatten (TKm.vlab-φ K.cod))
                      (permute-via-vlab C.vlab (PermProp.map⁺ remap perm-g))))
        (≈-Term-trans
          (subst₂-HomTerm-irrel objUIP _
            (cong unflatten (vlab-φ-lemma remap C.vlab K.vlab remap-vlab
                               (pe-stack K (range K.nE) K.dom)))
            _ (cong unflatten (vlab-φ-lemma remap C.vlab K.vlab remap-vlab K.cod))
            (permute-via-vlab C.vlab (PermProp.map⁺ remap perm-g)))
          (pvv-relabel Kf remap C.vlab K.vlab remap-vlab perm-g))))

      Xc-twin
        : subst₂ HomTerm (cong unflatten (TKm.vlab-φ K.dom))
                          (cong unflatten (TKm.vlab-φ K.cod)) Xc
          ≈Term PG ∘ pterm-g
      Xc-twin =
        ≈-Term-trans
          (subst₂-resp-≈Term (cong unflatten (TKm.vlab-φ K.dom))
                             (cong unflatten (TKm.vlab-φ K.cod)) Xc-assoc)
        (≈-Term-trans
          (≡⇒≈Term
            (subst₂-HomTerm-∘-dist (cong unflatten (TKm.vlab-φ K.dom)) MK1
              (cong unflatten (TKm.vlab-φ K.cod))
              (permute-via-vlab C.vlab combP) kterm-canon))
          (∘-resp-≈ kperm' ktwin'))

      domG = cong unflatten (⟪⟫-domL g)
      codG = cong unflatten (⟪⟫-codL g)

      Kpart : subst₂ HomTerm midGF codGF Xc ≈Term decode g
      Kpart =
        ≈-Term-trans
          (subst₂-HomTerm-irrel objUIP midGF
            (trans (cong unflatten (TKm.vlab-φ K.dom)) domG)
            codGF (trans (cong unflatten (TKm.vlab-φ K.cod)) codG) Xc)
        (≈-Term-trans
          (≡⇒≈Term (sym (subst₂-HomTerm-∘
                          (cong unflatten (TKm.vlab-φ K.dom)) domG
                          (cong unflatten (TKm.vlab-φ K.cod)) codG Xc)))
        (≈-Term-trans
          (subst₂-resp-≈Term domG codG Xc-twin)
          (≈-Term-sym decode-g-≈)))

      -- The whole `Pcomposite` C-transform (steps 1–4), as one `≈Term`.
      Pcomp-eq : PC ∘ Pcomposite ≈Term Xc ∘ Yc
      Pcomp-eq =
        ≈-Term-trans step1
          (≈-Term-trans step2 (≈-Term-trans step3 step4))

      goal : decode (g ∘ f) ≈Term decode g ∘ decode f
      goal =
        ≈-Term-trans decode-gf-≈
          (≈-Term-trans (subst₂-resp-≈Term domGF codGF Pcomp-eq)
            (≈-Term-trans (≡⇒≈Term step5)
              (∘-resp-≈ Kpart Gpart)))
