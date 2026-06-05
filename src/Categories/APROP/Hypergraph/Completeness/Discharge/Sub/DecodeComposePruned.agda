{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The PRUNED `∘` shape residual `decodeP-∘-shape`, PROVEN by mirroring
-- `Sub.DecodeComposeShape.decode-∘-shape-inner` with the UNPRUNED cospan
-- composition `hCompose` replaced by the PRUNED `hComposeP`:
--
--     decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f
--
-- Everything in the unpruned proof is generic in the hypergraph except the
-- `∘`-specific embedding data; we re-package that data via the
-- `hComposeP-impl` reduction lemmas (`injL = _↑ˡ count-non K.dom`,
-- `remapP`), feed the pruned `process-edges-↑ˡ-pure-L`
-- (`DecodeAttemptLinearP`) for the G-side pure-L stack, and reuse the
-- generic `StackEquivariance.process-edges-equivariant`,
-- `StackUniqueReach.*`, and `PermuteCoherenceK.*` exactly as the unpruned
-- proof does.
--
-- The two genuinely-pruned ingredients are imported from
-- `LinearHComposeP` (`remapP-injective`, `map-remapP-K-dom`) and
-- `DecodeAttemptLinearP` (`process-edges-↑ˡ-pure-L`).  The generic
-- term-twin gate `TermEmbed.process-edges-term-emb-gen`, the
-- `decode-attempt-extract` extraction, and `Linear⇒cod-Unique` are imported
-- from `ProcessEdgesTermShape` / `DecodeComposeShape`.
--
-- Parameterised by `objUIP` (UIP on `ObjTerm`) and `K : FaithfulnessResidual`
-- — the same two K-inputs threaded by the rest of the completeness chain.
--
-- No postulates: postulate-free over `objUIP` + `K`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposePruned
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; map-via-inj)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl
        ; domL-hComposeP; codL-hComposeP)
open import Categories.APROP.Hypergraph.Prune using (count-non)
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; process-all-edges
        ; decode-attempt; extract-exact)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (process-edges-++-stack)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj)

-- Pruned totality / pruned G-side pure-L lifting / pruned-Linear.
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP; ⟪⟫-LinearP; process-edges-↑ˡ-pure-L)
import Categories.APROP.Hypergraph.Completeness.Discharge.LinearHComposeP sig as LP

-- Generic term-twin gate + the importable extraction / Unique helpers.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (module TermEmbed; pe-term-++; pe-stack-++)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposeShape sig
  using (Linear⇒cod-Unique; decode-attempt-extract)
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

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  -- The pruned decoder `decodeP` (verbatim from `DecodeRelDecodeP`).
  decodeP : ∀ {A B} (f : HomTerm A B)
          → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  decodeP {A} {B} f =
    subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
           (proj₁ (decode-attempt-LinearP f))

  -- `subst₂ FlatGen` over a `trans · (sym ·)` cancels back.  (`--with-K`.)
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
  -- `permute` relabel-freeness (the `permute`-level twin), re-derived
  -- (verbatim from `DecodeComposeShape`'s private block).
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
-- ## Embedding data for `hComposeP ⟪f⟫ₚ ⟪g⟫ₚ`.
--
--   * G-side : φ = injL,  ψ = _↑ˡ K.nE   (injectivity from `inject+-inj cn`).
--   * K-side : φ = remapP, ψ = G.nE ↑ʳ_   (injectivity from `remapP-injective`).

module EmbedData
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  (G K : Hypergraph FlatGen) (bdy : codL G ≡ domL K)
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hComposeP G K bdy)
  open hComposeP-impl G K bdy

  C-hg : Hypergraph FlatGen
  C-hg = hComposeP G K bdy

  cn : ℕ
  cn = count-non K.dom

  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = LP.remapP-injective G K bdy lin-G lin-K

  ------------------------------------------------------------------------
  -- G-side embedding: φ = injL, ψ = _↑ˡ K.nE, H = G, J = C.
  ------------------------------------------------------------------------

  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  atom-einG : ∀ eG → map C.vlab (C.ein (ψG eG)) ≡ map G.vlab (G.ein eG)
  atom-einG eG = trans (cong (map vlab-P) (ein-c-inj₁-red eG))
                       (sym (map-via-inj vlab-injL (G.ein eG)))

  atom-eoutG : ∀ eG → map C.vlab (C.eout (ψG eG)) ≡ map G.vlab (G.eout eG)
  atom-eoutG eG = trans (cong (map vlab-P) (eout-c-inj₁-red eG))
                        (sym (map-via-inj vlab-injL (G.eout eG)))

  ψ-elabG : ∀ eG → subst₂ FlatGen (atom-einG eG) (atom-eoutG eG) (C.elab (ψG eG))
                 ≡ G.elab eG
  ψ-elabG eG =
    trans (subst₂-FlatGen-cancel
             (cong (map vlab-P) (ein-c-inj₁-red eG))
             (cong (map vlab-P) (eout-c-inj₁-red eG))
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

  module TG = TermEmbed {H = G} {J = hComposeP G K bdy} objUIP Kf
                injL (inject+-inj cn)
                vlab-injL
                ψG ein-c-inj₁-red eout-c-inj₁-red
                atom-einG atom-eoutG ψ-elabG

  ------------------------------------------------------------------------
  -- K-side embedding: φ = remapP, ψ = G.nE ↑ʳ_, H = K, J = C.
  ------------------------------------------------------------------------

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  atom-einK : ∀ eK → map C.vlab (C.ein (ψK eK)) ≡ map K.vlab (K.ein eK)
  atom-einK eK = trans (cong (map vlab-P) (ein-c-inj₂-red eK))
                       (sym (map-via-remapP (K.ein eK)))

  atom-eoutK : ∀ eK → map C.vlab (C.eout (ψK eK)) ≡ map K.vlab (K.eout eK)
  atom-eoutK eK = trans (cong (map vlab-P) (eout-c-inj₂-red eK))
                        (sym (map-via-remapP (K.eout eK)))

  ψ-elabK : ∀ eK → subst₂ FlatGen (atom-einK eK) (atom-eoutK eK) (C.elab (ψK eK))
                 ≡ K.elab eK
  ψ-elabK eK =
    trans (subst₂-FlatGen-cancel
             (cong (map vlab-P) (ein-c-inj₂-red eK))
             (cong (map vlab-P) (eout-c-inj₂-red eK))
             (map-via-remapP (K.ein eK))
             (map-via-remapP (K.eout eK))
             (elab-c (G.nE ↑ʳ eK)))
          (trans (cong (subst₂ FlatGen
                          (sym (map-via-remapP (K.ein eK)))
                          (sym (map-via-remapP (K.eout eK))))
                       (elab-c-inj₂ eK))
                 (subst₂-FlatGen-cancel′
                    (map-via-remapP (K.ein eK))
                    (map-via-remapP (K.eout eK))
                    (K.elab eK)))

  module TK = TermEmbed {H = K} {J = hComposeP G K bdy} objUIP Kf
                remapP remapP-injective
                remapP-vlab
                ψK ein-c-inj₂-red eout-c-inj₂-red
                atom-einK atom-eoutK ψ-elabK

--------------------------------------------------------------------------------
-- ## The main assembly (mirror of `DecodeComposeShape.decode-∘-shape-inner`).

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where
  open FaithfulnessResidual Kf using (permute-resp-≅↭)

  decodeP-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f
  decodeP-∘-shape {A} {B} {C₀} g f = goal
    where
      G K : Hypergraph FlatGen
      G = ⟪ f ⟫ₚ
      K = ⟪ g ⟫ₚ
      module G = Hypergraph G
      module K = Hypergraph K

      bdy : codL G ≡ domL K
      bdy = trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g))

      Chg : Hypergraph FlatGen
      Chg = hComposeP G K bdy
      module C = Hypergraph Chg

      lin-G : Lin.Linear G
      lin-G = ⟪⟫-LinearP f
      lin-K : Lin.Linear K
      lin-K = ⟪⟫-LinearP g

      open EmbedData objUIP Kf G K bdy lin-G lin-K
      open hComposeP-impl G K bdy using (injL; remapP; map-via-remapP; vlab-injL; remapP-vlab)

      -- pe-stack abbreviation.
      pe-stack : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nE H))
               → List (Fin (Hypergraph.nV H)) → List (Fin (Hypergraph.nV H))
      pe-stack H o s = proj₁ (process-edges H o s)

      -- The composite's whole-run inner term, extracted with its perm.
      ext-C = decode-attempt-extract Chg
                (proj₁ (decode-attempt-LinearP (g ∘ f)))
                (proj₂ (decode-attempt-LinearP (g ∘ f)))
      perm-C = proj₁ ext-C
      ext-C-eq = proj₂ ext-C

      -- The two sub-decoders, extracted.
      ext-f = decode-attempt-extract G
                (proj₁ (decode-attempt-LinearP f)) (proj₂ (decode-attempt-LinearP f))
      perm-f = proj₁ ext-f
      ext-f-eq = proj₂ ext-f
      ext-g = decode-attempt-extract K
                (proj₁ (decode-attempt-LinearP g)) (proj₂ (decode-attempt-LinearP g))
      perm-g = proj₁ ext-g
      ext-g-eq = proj₂ ext-g

      -- Edge blocks.
      gblk = map (_↑ˡ K.nE) (range G.nE)
      kblk = map (G.nE ↑ʳ_) (range K.nE)

      -- C.dom = map injL G.dom (definitional).
      after-G : List (Fin C.nV)
      after-G = pe-stack Chg gblk C.dom

      ----------------------------------------------------------------
      -- The G-block term-twin (φ = injL).
      G-block-twin
        : subst₂ HomTerm
            (cong unflatten (TG.vlab-φ G.dom))
            (cong unflatten
              (trans (cong (map C.vlab) (TG.proc-stack-emb (range G.nE) G.dom))
                     (TG.vlab-φ (pe-stack G (range G.nE) G.dom))))
            (proj₂ (process-edges Chg gblk C.dom))
          ≈Term proj₂ (process-edges G (range G.nE) G.dom)
      G-block-twin = TG.process-edges-term-emb (range G.nE) G.dom

      -- The G-decoder's final stack.
      s_G_final : List (Fin G.nV)
      s_G_final = pe-stack G (range G.nE) G.dom

      -- `after-G ≡ map injL s_G_final` (G-edges leave a pure-L stack).
      after-G-≡ : after-G ≡ map injL s_G_final
      after-G-≡ = cong proj₁ (proj₂ (process-edges-↑ˡ-pure-L G K bdy lin-G lin-K
                                       (range G.nE) G.dom))

      -- `after-G ↭ map remapP K.dom` (the canonical K-input).
      after-G-↭ : after-G Perm.↭ map remapP K.dom
      after-G-↭ =
        Perm.↭-trans (Perm.↭-reflexive after-G-≡)
          (Perm.↭-trans (PermProp.map⁺ injL perm-f)
                        (Perm.↭-reflexive (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))))

      ----------------------------------------------------------------
      -- Reservoir for the K-block, from `Linear Chg` (= ⟪g∘f⟫ₚ-Linear).
      lin-C : Lin.Linear Chg
      lin-C = ⟪⟫-LinearP (g ∘ f)

      reservoir-K : SUR.Reservoir≤1 Chg kblk after-G
      reservoir-K =
        SUR.reservoir-split Chg gblk kblk C.dom
          (SUR.dom-reservoir-prov Chg (proj₂ lin-C) (gblk ++ kblk)
            (Perm.↭-reflexive (sym (Inv.range-++ G.nE K.nE))))

      equiv-K = SE.process-edges-equivariant Chg Kf kblk
                  after-G-↭ reservoir-K
      ρf-K = proj₁ equiv-K
      equiv-K-eq = proj₂ equiv-K

      ----------------------------------------------------------------
      -- The K-block term-twin (φ = remapP), on the CANONICAL start stack.
      K-block-twin
        : subst₂ HomTerm
            (cong unflatten (TK.vlab-φ K.dom))
            (cong unflatten
              (trans (cong (map C.vlab) (TK.proc-stack-emb (range K.nE) K.dom))
                     (TK.vlab-φ (pe-stack K (range K.nE) K.dom))))
            (proj₂ (process-edges Chg kblk (map remapP K.dom)))
          ≈Term proj₂ (process-edges K (range K.nE) K.dom)
      K-block-twin = TK.process-edges-term-emb (range K.nE) K.dom

      ----------------------------------------------------------------
      -- Run-split: the composite process-term factors into K-block ∘ G-block.
      coeC : ∀ {s s' : List (Fin C.nV)} → s ≡ s'
           → HomTerm (unflatten (map C.vlab C.dom)) (unflatten (map C.vlab s))
           → HomTerm (unflatten (map C.vlab C.dom)) (unflatten (map C.vlab s'))
      coeC eq = subst (λ z → HomTerm (unflatten (map C.vlab C.dom))
                                      (unflatten (map C.vlab z))) eq

      run-split-term
        : proj₂ (process-edges Chg (range C.nE) C.dom)
          ≈Term coeC (sym (cong (λ es → pe-stack Chg es C.dom)
                                (Inv.range-++ G.nE K.nE)))
                     (proj₂ (process-edges Chg (gblk ++ kblk) C.dom))
      run-split-term =
        elim (Inv.range-++ G.nE K.nE)
        where
          elim : ∀ {es : List (Fin C.nE)} (eq : range C.nE ≡ es)
               → proj₂ (process-edges Chg (range C.nE) C.dom)
                 ≈Term coeC (sym (cong (λ es' → pe-stack Chg es' C.dom) eq))
                            (proj₂ (process-edges Chg es C.dom))
          elim refl = ≈-Term-refl

      block-fact = pe-term-++ Chg gblk kblk C.dom

      ----------------------------------------------------------------
      -- Expose `decodeP` of each term as the subst₂-transport.
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

      decode-gf-≈
        : decodeP (g ∘ f) ≈Term
          subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL (g ∘ f)))
                         (cong unflatten (⟪⟫ₚ-codL (g ∘ f)))
            (permute-via-vlab C.vlab perm-C
             ∘ proj₂ (process-edges Chg (range C.nE) C.dom))
      decode-gf-≈ =
        ≡⇒≈Term (cong (subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL (g ∘ f)))
                                       (cong unflatten (⟪⟫ₚ-codL (g ∘ f))))
                      ext-C-eq)

      ----------------------------------------------------------------
      -- The codomain `Unique`s.
      uGcod : Unique G.cod
      uGcod = Linear⇒cod-Unique G lin-G
      uKcod : Unique K.cod
      uKcod = Linear⇒cod-Unique K lin-K
      uCcod : Unique C.cod
      uCcod = Linear⇒cod-Unique Chg lin-C

      permC-coh
        : ∀ {s : List (Fin C.nV)} (p q : s Perm.↭ C.cod)
        → permute-via-vlab C.vlab p ≈Term permute-via-vlab C.vlab q
      permC-coh p q = permute-via-vlab-≈Term-coherence-K Kf C.vlab uCcod p q

      gterm = proj₂ (process-edges Chg gblk C.dom)
      kterm-canon = proj₂ (process-edges Chg kblk (map remapP K.dom))
      pterm-f = proj₂ (process-edges G (range G.nE) G.dom)
      pterm-g = proj₂ (process-edges K (range K.nE) K.dom)

      PC = permute-via-vlab C.vlab perm-C
      Pcomposite = proj₂ (process-edges Chg (range C.nE) C.dom)

      kterm-aG = proj₂ (process-edges Chg kblk after-G)

      -- `Unique (map remapP K.dom)` (= `map injL G.cod`).
      uRemapKdom : Unique (map remapP K.dom)
      uRemapKdom =
        subst Unique (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))
          (UniqueProp.map⁺ (λ {x} {y} → inject+-inj cn {x} {y}) uGcod)

      permRemap-coh
        : ∀ {s : List (Fin C.nV)} (p q : s Perm.↭ map remapP K.dom)
        → permute-via-vlab C.vlab p ≈Term permute-via-vlab C.vlab q
      permRemap-coh p q =
        permute-via-vlab-≈Term-coherence-K Kf C.vlab uRemapKdom p q

      Cdom-obj = unflatten (map C.vlab C.dom)

      absorb-coe
        : ∀ {ys} {s s' : List (Fin C.nV)} (eq : s ≡ s')
            (perm : s' Perm.↭ ys)
            (t : HomTerm Cdom-obj (unflatten (map C.vlab s)))
        → permute-via-vlab C.vlab perm
            ∘ subst (λ z → HomTerm Cdom-obj (unflatten (map C.vlab z))) eq t
          ≈Term permute-via-vlab C.vlab (subst (λ z → z Perm.↭ ys) (sym eq) perm) ∘ t
      absorb-coe refl perm t = ≈-Term-refl

      eqRS = sym (cong (λ es → pe-stack Chg es C.dom) (Inv.range-++ G.nE K.nE))
      perm-C1 = subst (λ z → z Perm.↭ C.cod) (sym eqRS) perm-C

      step1 : PC ∘ Pcomposite
            ≈Term permute-via-vlab C.vlab perm-C1
                    ∘ proj₂ (process-edges Chg (gblk ++ kblk) C.dom)
      step1 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl run-split-term)
                           (absorb-coe eqRS perm-C
                              (proj₂ (process-edges Chg (gblk ++ kblk) C.dom)))

      eqBF = sym (pe-stack-++ Chg gblk kblk C.dom)
      perm-C2 = subst (λ z → z Perm.↭ C.cod) (sym eqBF) perm-C1

      step2 : permute-via-vlab C.vlab perm-C1
                ∘ proj₂ (process-edges Chg (gblk ++ kblk) C.dom)
            ≈Term permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
      step2 = ≈-Term-trans (∘-resp-≈ ≈-Term-refl block-fact)
                           (absorb-coe eqBF perm-C1 (kterm-aG ∘ gterm))

      step3 : permute-via-vlab C.vlab perm-C2 ∘ (kterm-aG ∘ gterm)
            ≈Term permute-via-vlab C.vlab perm-C2
                    ∘ ((permute-via-vlab C.vlab (Perm.↭-sym ρf-K)
                        ∘ (kterm-canon ∘ permute-via-vlab C.vlab after-G-↭))
                       ∘ gterm)
      step3 = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ equiv-K-eq ≈-Term-refl)

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

      domGF = cong unflatten (⟪⟫ₚ-domL (g ∘ f))
      codGF = cong unflatten (⟪⟫ₚ-codL (g ∘ f))

      midList : map C.vlab (map remapP K.dom) ≡ flatten B
      midList = trans (cong (map C.vlab) (LP.map-remapP-K-dom G K bdy lin-G lin-K))
                      (trans (TG.vlab-φ G.cod) (⟪⟫ₚ-codL f))
      midGF = cong unflatten midList

      step5 : subst₂ HomTerm domGF codGF (Xc ∘ Yc)
            ≡ subst₂ HomTerm midGF codGF Xc ∘ subst₂ HomTerm domGF midGF Yc
      step5 = subst₂-HomTerm-∘-dist domGF midGF codGF Xc Yc

      ----------------------------------------------------------------
      -- The G-block twin codomain proof.
      M1 = cong unflatten
             (trans (cong (map C.vlab) (TG.proc-stack-emb (range G.nE) G.dom))
                    (TG.vlab-φ s_G_final))

      gtwin' : subst₂ HomTerm (cong unflatten (TG.vlab-φ G.dom)) M1 gterm
             ≈Term pterm-f
      gtwin' = G-block-twin

      ----------------------------------------------------------------
      -- The G-block permute reconciliation.
      midG-cod : map C.vlab (map remapP K.dom) ≡ map G.vlab G.cod
      midG-cod = trans (cong (map C.vlab) (LP.map-remapP-K-dom G K bdy lin-G lin-K))
                       (TG.vlab-φ G.cod)

      injf-↭ : after-G Perm.↭ map remapP K.dom
      injf-↭ = subst₂ Perm._↭_ (sym after-G-≡) (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))
                 (PermProp.map⁺ injL perm-f)

      injf-↭-pvv
        : permute-via-vlab C.vlab injf-↭
          ≡ subst₂ HomTerm
              (cong unflatten (cong (map C.vlab) (sym after-G-≡)))
              (cong unflatten (cong (map C.vlab) (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))))
              (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f))
      injf-↭-pvv =
        trans (cong permute (map⁺-subst₂ C.vlab (sym after-G-≡) (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))
                               (PermProp.map⁺ injL perm-f)))
              (sym (permute-subst₂ (cong (map C.vlab) (sym after-G-≡))
                                   (cong (map C.vlab) (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K)))
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
                      (cong unflatten (cong (map C.vlab) (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))))
                      (cong unflatten midG-cod)
                      (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f))))
        (≈-Term-trans
          (subst₂-HomTerm-irrel objUIP _
            (cong unflatten (vlab-φ-lemma injL C.vlab G.vlab vlab-injL s_G_final))
            _ (cong unflatten (vlab-φ-lemma injL C.vlab G.vlab vlab-injL G.cod))
            (permute-via-vlab C.vlab (PermProp.map⁺ injL perm-f)))
          (pvv-relabel Kf injL C.vlab G.vlab vlab-injL perm-f))))

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

      domF = cong unflatten (⟪⟫ₚ-domL f)
      codF = cong unflatten (⟪⟫ₚ-codL f)

      Gpart : subst₂ HomTerm domGF midGF Yc ≈Term decodeP f
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
      combP : pe-stack Chg kblk (map remapP K.dom) Perm.↭ C.cod
      combP = Perm.trans (Perm.↭-sym ρf-K) perm-C2

      Xc-assoc : Xc ≈Term permute-via-vlab C.vlab combP ∘ kterm-canon
      Xc-assoc = ≈-Term-sym assoc

      MK1 = cong unflatten
              (trans (cong (map C.vlab) (TK.proc-stack-emb (range K.nE) K.dom))
                     (TK.vlab-φ (pe-stack K (range K.nE) K.dom)))

      ktwin' : subst₂ HomTerm (cong unflatten (TK.vlab-φ K.dom)) MK1 kterm-canon
             ≈Term pterm-g
      ktwin' = K-block-twin

      PG = permute-via-vlab K.vlab perm-g

      proc-stack-emb-K
        : pe-stack Chg kblk (map remapP K.dom)
          ≡ map remapP (pe-stack K (range K.nE) K.dom)
      proc-stack-emb-K = TK.proc-stack-emb (range K.nE) K.dom

      remapg-↭ : pe-stack Chg kblk (map remapP K.dom) Perm.↭ C.cod
      remapg-↭ = subst₂ Perm._↭_ (sym proc-stack-emb-K) refl
                   (PermProp.map⁺ remapP perm-g)

      remapg-↭-pvv
        : permute-via-vlab C.vlab remapg-↭
          ≡ subst₂ HomTerm
              (cong unflatten (cong (map C.vlab) (sym proc-stack-emb-K)))
              (cong unflatten (cong (map C.vlab) refl))
              (permute-via-vlab C.vlab (PermProp.map⁺ remapP perm-g))
      remapg-↭-pvv =
        trans (cong permute (map⁺-subst₂ C.vlab (sym proc-stack-emb-K) refl
                               (PermProp.map⁺ remapP perm-g)))
              (sym (permute-subst₂ (cong (map C.vlab) (sym proc-stack-emb-K))
                                   (cong (map C.vlab) refl)
                                   (PermProp.map⁺ C.vlab (PermProp.map⁺ remapP perm-g))))

      kperm'
        : subst₂ HomTerm MK1 (cong unflatten (TK.vlab-φ K.cod))
            (permute-via-vlab C.vlab combP)
          ≈Term PG
      kperm' =
        ≈-Term-trans
          (subst₂-resp-≈Term MK1 (cong unflatten (TK.vlab-φ K.cod))
            (permC-coh combP remapg-↭))
        (≈-Term-trans
          (≡⇒≈Term (cong (subst₂ HomTerm MK1 (cong unflatten (TK.vlab-φ K.cod)))
                         remapg-↭-pvv))
        (≈-Term-trans
          (≡⇒≈Term (subst₂-HomTerm-∘
                      (cong unflatten (cong (map C.vlab) (sym proc-stack-emb-K))) MK1
                      (cong unflatten (cong (map C.vlab) refl))
                      (cong unflatten (TK.vlab-φ K.cod))
                      (permute-via-vlab C.vlab (PermProp.map⁺ remapP perm-g))))
        (≈-Term-trans
          (subst₂-HomTerm-irrel objUIP _
            (cong unflatten (vlab-φ-lemma remapP C.vlab K.vlab remapP-vlab
                               (pe-stack K (range K.nE) K.dom)))
            _ (cong unflatten (vlab-φ-lemma remapP C.vlab K.vlab remapP-vlab K.cod))
            (permute-via-vlab C.vlab (PermProp.map⁺ remapP perm-g)))
          (pvv-relabel Kf remapP C.vlab K.vlab remapP-vlab perm-g))))

      Xc-twin
        : subst₂ HomTerm (cong unflatten (TK.vlab-φ K.dom))
                          (cong unflatten (TK.vlab-φ K.cod)) Xc
          ≈Term PG ∘ pterm-g
      Xc-twin =
        ≈-Term-trans
          (subst₂-resp-≈Term (cong unflatten (TK.vlab-φ K.dom))
                             (cong unflatten (TK.vlab-φ K.cod)) Xc-assoc)
        (≈-Term-trans
          (≡⇒≈Term
            (subst₂-HomTerm-∘-dist (cong unflatten (TK.vlab-φ K.dom)) MK1
              (cong unflatten (TK.vlab-φ K.cod))
              (permute-via-vlab C.vlab combP) kterm-canon))
          (∘-resp-≈ kperm' ktwin'))

      domG = cong unflatten (⟪⟫ₚ-domL g)
      codG = cong unflatten (⟪⟫ₚ-codL g)

      Kpart : subst₂ HomTerm midGF codGF Xc ≈Term decodeP g
      Kpart =
        ≈-Term-trans
          (subst₂-HomTerm-irrel objUIP midGF
            (trans (cong unflatten (TK.vlab-φ K.dom)) domG)
            codGF (trans (cong unflatten (TK.vlab-φ K.cod)) codG) Xc)
        (≈-Term-trans
          (≡⇒≈Term (sym (subst₂-HomTerm-∘
                          (cong unflatten (TK.vlab-φ K.dom)) domG
                          (cong unflatten (TK.vlab-φ K.cod)) codG Xc)))
        (≈-Term-trans
          (subst₂-resp-≈Term domG codG Xc-twin)
          (≈-Term-sym decode-g-≈)))

      Pcomp-eq : PC ∘ Pcomposite ≈Term Xc ∘ Yc
      Pcomp-eq =
        ≈-Term-trans step1
          (≈-Term-trans step2 (≈-Term-trans step3 step4))

      goal : decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f
      goal =
        ≈-Term-trans decode-gf-≈
          (≈-Term-trans (subst₂-resp-≈Term domGF codGF Pcomp-eq)
            (≈-Term-trans (≡⇒≈Term step5)
              (∘-resp-≈ Kpart Gpart)))
