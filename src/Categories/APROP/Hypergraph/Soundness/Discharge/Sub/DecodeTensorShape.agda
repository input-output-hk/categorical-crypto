{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The generic (decoder-agnostic) `⊗` shape assembly `DecodeShapeGeneric`,
-- instantiated by `DecodeTensorPruned.decodeP-⊗-shape`:
--
--   decodeP (f ⊗₁ g)
--     ≈Term to(unflatten-++-≅ (flatten B) (flatten D))
--            ∘ (decodeP f ⊗₁ decodeP g)
--            ∘ from(unflatten-++-≅ (flatten A) (flatten C))
--
-- Postulate-free over `objUIP` + `K : FaithfulnessResidual`.  Key pieces:
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
--     mid-collapse).
--   * `BoxAssoc.box-braid` — the σ-mirror of `box-suffix`: a front-acting
--     box on `P ++ rest` factors as the box held AFTER `P`, conjugated by
--     block-swap braids.  Uses one-box symmetry-naturality + σ∘σ≈id +
--     α-coherence (NOT the two-box `nf-bracket` kernel).
--   * `EmbedData.{TG,TK}` — G-/K-side `TermEmbed` gate instances.
--
-- DESIGN: unlike the `∘` case (where `C.dom` is a pure φ-image and the gate
-- applies directly), the `⊗` blocks run on the disjoint mixed dom
-- `map injL G.dom ++ map injR K.dom`, so each block term is first sliced as
-- `(canonical run ⊗₁ id)` / `(id ⊗₁ canonical run)` by a per-edge box-of
-- suffix/prefix coherence induction before the gate and `pvv-block-tensor`
-- apply.  Parameterised by `objUIP` and `K : FaithfulnessResidual`.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeTensorShape
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hTensor
        ; map-via-inj; map-via-raise)
import Categories.APROP.Hypergraph.FromAPROP sig as FA
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-edges; edge-step; extract-prefix; extract-elem; process-all-edges
        ; decode-attempt; extract-exact)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using ( process-edges-↑ˡ-on-mixed; process-edges-↑ʳ-on-perm
        ; edge-step-↑ˡ-on-mixed; edge-step-↑ˡ-on-mixed-just
        ; edge-step-↑ˡ-on-mixed-nothing
        ; edge-step-↑ʳ-on-mixed-just; edge-step-↑ʳ-on-mixed-nothing
        ; edge-step-↑ʳ-on-perm)
open import Categories.APROP.Hypergraph.Soundness.DecodeProperties sig
  using (extract-prefix-↑ˡ-on-mixed-just; extract-prefix-↑ˡ-on-mixed-nothing
        ; extract-prefix-via-injective-just; extract-prefix-via-injective-nothing
        ; extract-prefix-↑ʳ-on-mixed-just; extract-prefix-↑ʳ-on-mixed-nothing
        ; extract-prefix-↭-residual; extract-prefix-↭-nothing)
import Categories.APROP.Hypergraph.Soundness.Linearity sig as Lin
import Categories.APROP.Hypergraph.Invariant sig as Inv

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.ProcessEdgesTermShape sig
  using (module TermEmbed; pe-term-++; pe-stack-++)
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidEquivariant sig as FME
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData _≟X_ as BNB
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData _≟X_ as BNV
open import Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons sig
  using (c-iso-assoc-from)
open import Categories.APROP.Hypergraph.Soundness.UnflattenMonoidal sig
  using (c-iso-assoc-to; cancel-mid-iso; conj-lemma; bridge-dom; bridge-cod
        ; to-uf-cong; from-uf-cong; subst-2)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of
        ; edge-step-graph)

-- The `unflatten-++-≅` box-reassociation cone, extracted into a leaf module.
-- Re-exposes only the submodules `BlockTensor` / `BoxAssoc` / `BlockBoxSuffix`
-- (their qualified references below resolve through this open).
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BoxKernel sig _≟X_
  using (module BlockTensor; module BoxAssoc)

-- The generic, proven (postulate-free, --safe) "separable-stack" factorization
-- for the decoder's `process-edges`.  Instantiated at `H := hTensor G K` it IS
-- the G-side `gblock-factor` (the `injL`-edge block touches only `injL`
-- vertices, which are disjoint from the `injR`-residual `map injR ys`), so the
-- per-edge G-side machinery is replaced by one call to `process-edges-separable`.
-- NOT a cycle: `SeparableSpike` imports the lightweight `BoxKernel` leaf, not
-- `DecodeTensorShape`.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SeparableSpike sig _≟X_
  as SS

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective; splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin.Properties as FinP
import Axiom.UniquenessOfIdentityProofs as UIPmod
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Properties using () renaming (≡-dec to List-≡-dec)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
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

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using ( subst₂-FlatGen-cancel; subst₂-FlatGen-cancel′
        ; subst₂-HomTerm-irrel; subst₂-HomTerm-∘; subst₂-resp-≈Term
        ; subst₂-HomTerm-∘-dist; subst₂-⊗₁-dist
        ; permute-subst₂
        ; pvv-relabel
        ; just≢nothing
        ; Linear⇒cod-Unique; decode-attempt-extract )

private
  module FM = Category FreeMonoidal



-- Library iso-cancellation combinators (agda-categories), for the
-- `unflatten-++-≅` `from ∘ to ≈ id` eliminations.
open import Categories.Morphism.Reasoning FreeMonoidal using (cancelˡ; cancelʳ)

--------------------------------------------------------------------------------
-- ## Embedding data for `hTensor G K`.  The tensor admits two injective
-- label-preserving sub-hypergraph embeddings, packaged as `TermEmbed`
-- parameters:
--   * G-side : φ = injL,  ψ = _↑ˡ K.nE.
--   * K-side : φ = injR,  ψ = G.nE ↑ʳ_.

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

  -- G-side embedding: φ = injL, ψ = _↑ˡ K.nE, H = G, J = C.

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
-- ## The G-side / K-side block factorizations — SHARED SCAFFOLDING.
--
-- The G-side `gblock-factor` (term companion of `process-edges-↑ˡ-on-mixed`)
-- and K-side `kblock-factor` (companion of `process-edges-↑ʳ-on-perm`).
-- This module fixes the framing convention (`BTC.uf++`) and the factored-
-- form shapes (`GFactored`, `Lterm`, `KFactored`, `KClean`, `Kterm`) those
-- inductions land on, plus the stack agreements and per-edge residual
-- rewrites they consume.

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
  -- ### Milestone 2a — the G-side SUFFIX-CARRY factorization (at the C
  -- level, no G/K relabel).  Relates the mixed-stack C-run of the G-edge
  -- block to the pure-L C-run tensored with `id` on the constant
  -- `map injR ys` suffix.  Per FIRE edge the box factors via
  -- `BoxAssoc.box-suffix`; per SKIP edge as `id ⊗₁ id`.

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

  -- UIP on the vertex-list type, via Hedberg (decidable equality on
  -- `List (Fin C.nV)`), under `--without-K`.
  uipL : ∀ {a b : List (Fin C.nV)} (p q : a ≡ b) → p ≡ q
  uipL = UIPmod.Decidable⇒UIP.≡-irrelevant (List-≡-dec FinP._≟_)

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
  -- ### `to-BTC` / `from-BTC` — the `BTC.uf++` to/from in terms of the raw
  -- `unflatten-++-≅` on `List X`, bridging the `map-++ C.vlab` reconciliation
  -- via `BNB.to-subst₂-≅`/`from-subst₂-≅`.  (Consumed by the K-side
  -- `box-prefix-BTC` and the final assembly.)
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

  ------------------------------------------------------------------------
  -- ### `head-factor-K` — K-side single-edge FIRE factorization (mirror of
  -- `head-factor` with LEFT/RIGHT swapped: the carried block is the LEFT
  -- G-output prefix `map injL P` held by `id`, the box acts on the RIGHT
  -- injR-block).  For a FIRE K-edge from `map injL P ++ map injR ys`, the
  -- head factors — modulo `BTC.uf++` framing — as `(id {prefix} ⊗₁ K-head)`.
  -- Box half = `box-prefix-BTC`; permute half = `head-perm-factor-K`;
  -- combine = middle iso-cancellation + `⊗-∘-dist`.

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
            ≡R.≡⟨ cong₃ (λ a b c → a ∘ b ∘ c) to-eo-≡ mid-≡ from-ei-≡ ⟩
          subst₂ HomTerm Qto Rc to-raw
            ∘ subst₂ HomTerm Qfr Qto M
            ∘ subst₂ HomTerm Pp Qfr fr-raw
            ≡R.≡⟨ cong (λ w → subst₂ HomTerm Qto Rc to-raw ∘ w)
                    (sym (subst₂-HomTerm-∘-dist Pp Qfr Qto M fr-raw)) ⟩
          subst₂ HomTerm Qto Rc to-raw
            ∘ subst₂ HomTerm Pp Qto (M ∘ fr-raw)
            ≡R.≡⟨ sym (subst₂-HomTerm-∘-dist Pp Qto Rc to-raw (M ∘ fr-raw)) ⟩
          subst₂ HomTerm Pp Rc (to-raw ∘ M ∘ fr-raw)
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
            (subst₂ HomTerm (cong unflatten Aei) (cong unflatten Aeo)
               (to-raw ∘ M ∘ fr-raw))
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
  -- ### `head-factor-K` — single-K-edge FIRE head-step factorization
  -- (non-inductive, mirror of `head-factor`).  A FIRE K-edge from
  -- `map injL P ++ map injR ys` — its `box-prefix`-LHS-shaped box
  -- precomposed with the front-permute (identity on the LEFT prefix) —
  -- factors, modulo `BTC.uf++` framing, as `(id {prefix} ⊗₁ K-head)` where
  --   K-head = (box on the injR-block residual) ∘ pvlC q.
  -- Box half = `box-prefix-BTC`; permute half = `head-perm-factor-K`;
  -- combine = middle iso-cancellation + `⊗-∘-dist`.
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

  -- `coeC` (codomain transport) distributes over `∘` on the cod factor.
  coeC-∘
    : ∀ {d m : List (Fin C.nV)} {s s' : List (Fin C.nV)} (eq : s ≡ s')
        (f : HomTerm (unflatten (map C.vlab m)) (unflatten (map C.vlab s)))
        (g : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab m)))
    → coeC {d} eq (f ∘ g) ≡ coeC {m} eq f ∘ g
  coeC-∘ refl f g = refl

  ------------------------------------------------------------------------
  -- ### `gblock-factor` via the generic `SeparableSpike.process-edges-separable`.
  --
  -- The G-edge block (`map ψG es`, `ψG = _↑ˡ K.nE`) touches ONLY `injL`
  -- vertices — `C.ein (ψG e) = map injL (G.ein e)` — which are DISJOINT from
  -- the `injR`-residual `map injR ys` (no `injL k` is an `injR j`).  So the
  -- generic separability theorem applies verbatim at `H := hTensor G K`,
  -- `es := map ψG es`, `xs := map injL xs`, `R := map injR ys`, and the
  -- per-edge G-side machinery (`head-factor`/`fire-core`/`fire-case`/
  -- `edge-suffix-factor` + the cons induction) collapses to one call.

  -- `injL k` and `injR j` are distinct: `splitAt G.nV` sends them to `inj₁`
  -- vs `inj₂`.
  injL≢injR : ∀ {k : Fin G.nV} {j : Fin K.nV} → injL k ≡ injR j → ⊥
  injL≢injR {k} {j} eq with trans (sym (splitAt-↑ˡ G.nV k K.nV))
                              (trans (cong (splitAt G.nV) eq)
                                     (splitAt-↑ʳ G.nV K.nV j))
  ... | ()

  -- `injL k` is absent from a `map injR`-list (induction on `ys`; the head
  -- test `injR y ≟ injL k` is always `no` by `injL≢injR`).
  injL∉injRs : ∀ (k : Fin G.nV) (ys : List (Fin K.nV))
             → extract-elem (injL k) (map injR ys) ≡ nothing
  injL∉injRs k []       = refl
  injL∉injRs k (y ∷ ys) with injR y FinP.≟ injL k
  ... | yes p  = ⊥-elim (injL≢injR (sym p))
  ... | no  _  rewrite injL∉injRs k ys = refl

  -- Every input vertex of a G-edge `ψG e` is absent from `map injR ys`:
  -- `C.ein (ψG e) = map injL (G.ein e)`, each entry an `injL`.
  ein-disjointG : ∀ (e : Fin G.nE) (ys : List (Fin K.nV))
                → SS.ein-disjoint C-hg (ψG e) (map injR ys)
  ein-disjointG e ys =
    subst (λ ks → All (λ k → extract-elem k (map injR ys) ≡ nothing) ks)
          (sym (ein-c-inj₁-red e))
          (all-injL (G.ein e))
    where
      all-injL : ∀ (ks : List (Fin G.nV))
               → All (λ k → extract-elem k (map injR ys) ≡ nothing) (map injL ks)
      all-injL []       = []ᴬ
      all-injL (k ∷ ks) = injL∉injRs k ys ∷ᴬ all-injL ks

  -- The whole G-block is disjoint from the `injR`-residual.
  g-disjoint : ∀ (es : List (Fin G.nE)) (ys : List (Fin K.nV))
             → SS.block-disjoint C-hg (map ψG es) (map injR ys)
  g-disjoint []       ys = []ᴬ
  g-disjoint (e ∷ es) ys = ein-disjointG e ys ∷ᴬ g-disjoint es ys

  -- `SS.coe-cod` (pattern-match codomain transport) IS `coeC` (the `subst`
  -- codomain transport) — both reduce to identity on `refl`.
  coe-cod≡coeC : ∀ {d s s' : List (Fin C.nV)} (eq : s ≡ s')
                   (t : HomTerm (unflatten (map C.vlab d)) (unflatten (map C.vlab s)))
               → SS.coe-cod C-hg {d} eq t ≡ coeC {d} eq t
  coe-cod≡coeC refl t = refl

  -- The bridge: `process-edges-separable`'s `Factored` (block-1 framed at the
  -- raw C-run stack `pe-stackC (map ψG es) (map injL xs)`) re-indexed along the
  -- pure-L stack agreement `proc-stack-emb-L` IS `GFactored` (block-1 = `Lterm`
  -- framed at `map injL (pe-stackG es xs)`).  Generalise the block-1 codomain
  -- list `A`, the stack-emb `e`, and the whole-stack agreement `wEq`, then
  -- match `e` at `refl`: `Lterm` becomes the raw C-run, the two framings
  -- coincide, and `wEq`/`process-edges-stack-sep` (both proving the SAME
  -- equation `… ≡ A ++ map injR ys`) collapse by `uipL`/`coe-cod≡coeC`.
  gf-bridge
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
        (dis : SS.block-disjoint C-hg (map ψG es) (map injR ys))
        {A : List (Fin C.nV)} (e : pe-stackC (map (_↑ˡ K.nE) es) (map injL xs) ≡ A)
        (wEq : pe-stackC (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys)
               ≡ A ++ map injR ys)
    → coeC {map injL xs ++ map injR ys} wEq
        (pe-termC (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys))
      ≈Term _≅_.to (BTC.uf++ A (map injR ys))
            ∘ (coeC {map injL xs} e (pe-termC (map (_↑ˡ K.nE) es) (map injL xs))
               ⊗₁ id {RsufObj ys})
            ∘ _≅_.from (BTC.uf++ (map injL xs) (map injR ys))
  gf-bridge es xs ys dis refl wEq =
    ≈-Term-trans (≡⇒≈Term lhs-align) (SS.process-edges-separable C-hg (map ψG es)
                                        (map injL xs) (map injR ys) dis)
    where
      -- LHS: `coeC wEq` and `SS.coe-cod (process-edges-stack-sep)` are
      -- codomain-substs on the SAME equation `pe-stackC (map ψG es) (map injL
      -- xs ++ map injR ys) ≡ pe-stackC (map ψG es) (map injL xs) ++ map injR
      -- ys`, so they coincide (`coe-cod≡coeC` + `uipL`).
      lhs-align
        : coeC {map injL xs ++ map injR ys} wEq
            (pe-termC (map ψG es) (map injL xs ++ map injR ys))
          ≡ SS.coe-cod C-hg {map injL xs ++ map injR ys}
              (SS.process-edges-stack-sep C-hg (map ψG es)
                 (map injL xs) (map injR ys) dis)
              (pe-termC (map ψG es) (map injL xs ++ map injR ys))
      lhs-align =
        trans (cong (λ z → coeC {map injL xs ++ map injR ys} z
                              (pe-termC (map ψG es) (map injL xs ++ map injR ys)))
                    (uipL wEq
                          (SS.process-edges-stack-sep C-hg (map ψG es)
                             (map injL xs) (map injR ys) dis)))
              (sym (coe-cod≡coeC
                      (SS.process-edges-stack-sep C-hg (map ψG es)
                         (map injL xs) (map injR ys) dis)
                      (pe-termC (map ψG es) (map injL xs ++ map injR ys))))

  -- `gblock-factor` keeps its statement (and `gterm-GF` is unchanged); its
  -- proof is now `gf-bridge` at the pure-L stack agreement `proc-stack-emb-L`,
  -- whole-stack agreement `mixed-stack-G`.  `GFactored es xs ys` IS the
  -- `gf-bridge` RHS at `A := map injL (pe-stackG es xs)`, `e := proc-stack-emb-L
  -- es xs` (`Lterm es xs` unfolds to that `coeC`).  The `Reservoir≤1`
  -- hypothesis is no longer needed (kept in the type for an unchanged public
  -- interface).
  gblock-factor
    : (es : List (Fin G.nE)) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → SUR.Reservoir≤1 (hTensor G K) (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys)
    → coeC {map injL xs ++ map injR ys} (mixed-stack-G es xs ys)
        (pe-termC (map (_↑ˡ K.nE) es) (map injL xs ++ map injR ys))
      ≈Term GFactored es xs ys
  gblock-factor es xs ys _ =
    gf-bridge es xs ys (g-disjoint es ys) (proc-stack-emb-L es xs)
              (mixed-stack-G es xs ys)


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
  -- ### Shared subst-id (`sidX`) machinery.  A canonical subst-id morphism
  -- `sidX` (codomain transport of `id` over `unflatten`) into which
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

  -- `sidX`-fold normalizers: collapse a (left- or right-nested) product of
  -- `sidX` morphisms into a single `sidX e` for ANY target path `e` with the
  -- same endpoints (fold via `sidX-∘`, retarget via `sidX-irrel`).  These are
  -- the shared body of the four `right-eq`/`left-eq` boundary proofs in
  -- `Sin`/`Sout`, which differ only in nesting/factor-count and target.

  -- two factors:  `sidX p₂ ∘ sidX p₁ ≈ sidX e`.
  sidX-collapse₂ : ∀ {a b c : List X} (p₁ : a ≡ b) (p₂ : b ≡ c) (e : a ≡ c)
                 → sidX p₂ ∘ sidX p₁ ≈Term sidX e
  sidX-collapse₂ p₁ p₂ e =
    ≈-Term-trans (sidX-∘ p₁ p₂) (sidX-irrel (trans p₁ p₂) e)

  -- three factors, left-nested:  `(sidX p₃ ∘ sidX p₂) ∘ sidX p₁ ≈ sidX e`.
  sidX-collapse₃ˡ : ∀ {a b c d : List X}
                      (p₁ : a ≡ b) (p₂ : b ≡ c) (p₃ : c ≡ d) (e : a ≡ d)
                  → (sidX p₃ ∘ sidX p₂) ∘ sidX p₁ ≈Term sidX e
  sidX-collapse₃ˡ p₁ p₂ p₃ e =
    ≈-Term-trans (sidX-∘ p₂ p₃ ⟩∘⟨refl)
      (sidX-collapse₂ p₁ (trans p₂ p₃) e)

  -- three factors, right-nested:  `sidX p₃ ∘ (sidX p₂ ∘ sidX p₁) ≈ sidX e`.
  sidX-collapse₃ʳ : ∀ {a b c d : List X}
                      (p₁ : a ≡ b) (p₂ : b ≡ c) (p₃ : c ≡ d) (e : a ≡ d)
                  → sidX p₃ ∘ (sidX p₂ ∘ sidX p₁) ≈Term sidX e
  sidX-collapse₃ʳ p₁ p₂ p₃ e =
    ≈-Term-trans (refl⟩∘⟨ sidX-∘ p₁ p₂)
      (sidX-collapse₂ (trans p₁ p₂) p₃ e)

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
  -- into `map A ++ map B` (the `map-++ C.vlab A B` block-1 reconciliation).
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
        ≈⟨ refl⟩∘⟨ rawTo-blk1-split A B Cc ⟩∘⟨refl ⟩
      BoxAssoc.subst-id-cod (sym (map-++ C.vlab (A ++ B) Cc))
        ∘ (BoxAssoc.subst-id-cod (cong (_++ map C.vlab Cc) (sym (map-++ C.vlab A B)))
           ∘ rawTo₀ (map C.vlab A ++ map C.vlab B) (map C.vlab Cc))
        ∘ (rawTo₀ (map C.vlab A) (map C.vlab B) ⊗₁ id)
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
  -- ### `σin-as-pvl` — box-braid's input braid `σ-in` (at the `map C.vlab`
  -- block images) equals the `BTC.uf++`-framed `pvlC` of the block-shift
  -- permutation `shifts eiBlk Pblk rgBlk`, reframed onto the `map C.vlab`
  -- endpoints so the RHS is `from(uf++) ∘ pvlC(shifts)`.

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
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (α⇒ {Up} {Ue} {Ur} ∘ (rFrom pL eL ⊗₁ id {Ur}) ∘ rFrom (pL ++ eL) rL)
          ∘ BoxAssoc.subst-id-dom comb-out
          ≈⟨ refl⟩∘⟨ cif-assoc-out ⟩∘⟨refl ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
             ∘ BoxAssoc.subst-id-cod (++-assoc pL eL rL))
          ∘ BoxAssoc.subst-id-dom comb-out
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (((id {Up} ⊗₁ rFrom eL rL) ∘ rFrom pL (eL ++ rL))
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id {Up} ⊗₁ rTo eL rL)
          ∘ (id {Up} ⊗₁ rFrom eL rL)
          ∘ (rFrom pL (eL ++ rL)
             ∘ (BoxAssoc.subst-id-cod (++-assoc pL eL rL) ∘ BoxAssoc.subst-id-dom comb-out))
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
    -- Thin specialization of `BoxAssoc.conj-lemma`: at `refl refl` the
    -- `tcod`/`subst-id-dom` conjugators reduce to `id`, matching its body.
    subst₂-conj-tensor :
      ∀ {a b : List X} {c d : List X} (p : a ≡ b) (q : c ≡ d)
        (t : HomTerm (unflatten a) (Up ⊗₀ unflatten c))
      → subst₂ HomTerm (cong unflatten p) (cong (Up ⊗₀_) (cong unflatten q)) t
        ≈Term tcod q ∘ t ∘ BoxAssoc.subst-id-dom p
    subst₂-conj-tensor refl refl t = conj-lemma refl refl t


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
          ≈⟨ sidX-collapse₃ˡ (sym dom-list) (sym (++-assoc eL pL rL)) (sym (sym comb-in))
                             (cong (map C.vlab) (sym (++-assoc eiBlk Pblk rgBlk))) ⟩
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
          ≈⟨ sidX-collapse₂ (sym comb-out) (++-assoc pL eL rL)
                            (trans (cong (map C.vlab) (++-assoc Pblk eiBlk rgBlk)) (sym dom-uf)) ⟩
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
          ≈⟨ reassemble-left ⟩
        (_≅_.from (BTC.uf++ Pblk (eiBlk ++ rgBlk)) ∘ sidC (++-assoc Pblk eiBlk rgBlk))
          ∘ pvlC (BNV.app-swap C.vlab eiBlk Pblk rgBlk)
          ∘ sidC (sym (++-assoc eiBlk Pblk rgBlk))
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
              ≈⟨ (FM.assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
            (((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ dCI ∘ cAs)
              ∘ dDL
              ≈⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ ((pA ∘ dCI ∘ cAs) ∘ dDL)
              ≈⟨ refl⟩∘⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ ((dCI ∘ cAs) ∘ dDL)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
            ((tcod cod-list ∘ rFrom pL (eL ++ rL)) ∘ (cA ∘ dCO))
              ∘ pA ∘ (dCI ∘ cAs ∘ dDL)
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
  -- ### `σout-as-pvl` — the DUAL of `σin-as-pvl` (box-braid's OUTPUT braid
  -- `σ-out` equals `pvlC`-of-`shifts` post-composed onto the `to` iso).
  -- Vertical mirror of `module Sin` (dom↔cod, to↔from, α⇒↔α⇐ swapped), using
  -- the `to`-orientation keystone / views / `c-iso-assoc-to`.

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
          ≈⟨ c-iso-assoc-to eL pL rL ⟩
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
          ≈⟨ c-iso-assoc-to pL eL rL ⟩
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
    -- Thin specialization of `BoxAssoc.conj-lemma`: at `refl refl` the
    -- `subst-id-cod`/`tdom` conjugators reduce to `id`, matching its body.
    subst₂-conj-tensor-dom :
      ∀ {a b : List X} {c d : List X} (p : a ≡ b) (q : c ≡ d)
        (t : HomTerm (Up ⊗₀ unflatten c) (unflatten a))
      → subst₂ HomTerm (cong (Up ⊗₀_) (cong unflatten q)) (cong unflatten p) t
        ≈Term BoxAssoc.subst-id-cod p ∘ t ∘ tdom q
    subst₂-conj-tensor-dom refl refl t = conj-lemma refl refl t

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
          ≈⟨ sidX-collapse₃ʳ (sym bridge-eo) (sym (sym (++-assoc eL pL rL))) dom-list
                             (cong (map C.vlab) (++-assoc eoBlk Pblk rgBlk)) ⟩
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
          ≈⟨ sidX-collapse₂ (sym (++-assoc pL eL rL)) bridge-Po
                            (trans cod-uf (cong (map C.vlab) (sym (++-assoc Pblk eoBlk rgBlk)))) ⟩
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
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ reassemble-right ⟩
        sidC (++-assoc eoBlk Pblk rgBlk)
          ∘ pvlC (BNV.app-swap C.vlab Pblk eoBlk rgBlk)
          ∘ (sidC (sym (++-assoc Pblk eoBlk rgBlk)) ∘ _≅_.to (BTC.uf++ Pblk (eoBlk ++ rgBlk)))
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
  -- block-swap braids rewritten into the `BTC.uf++`-framed `pvlC`-of-`shifts`
  -- form (via `Sin.σin-as-pvl` / `Sout.σout-as-pvl`).  The FRONT-acting box
  -- on the un-split residual `Pblk++rgBlk` factors as
  --   (pvlC(shifts Pblk eoBlk) ∘ to(uf++ Pblk (eoBlk++rgBlk)))
  --     ∘ (id {U Pblk} ⊗₁ BoxSub)
  --     ∘ (from(uf++ Pblk (eiBlk++rgBlk)) ∘ pvlC(shifts eiBlk Pblk))
  -- where `BoxSub` is the same pure-block box `head-factor-K` uses.  This is
  -- the per-FIRE-edge tool bringing the mixed FRONT box into
  -- `head-factor-K`'s prefix-held input for the K induction.
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
  -- ### Milestone 2b proper: `kblock-factor` — base cases.
  --
  -- `kblock-factor` goes through the generalised perm-tracking induction
  -- `kfac-gen`: the K-prepend wrinkle forbids a clean stack `≡`, so the
  -- actual stack `s` + a perm-to-clean `pf` are threaded (mirroring
  -- `process-edges-↑ʳ-on-perm`); `kblock-factor` is its `s = clean,
  -- pf = ↭-refl, Br = ↭-sym KBraid` instance.  The two base-case pieces —
  -- `KClean-nil` (the `es = []` target collapses to `id`) and `pvlC-cancel`
  -- (the round-trip `pvlC Br ∘ pvlC pf` collapses to `id`) — discharge `[]`.
  -- The cons step uses the `KClean`/`Kterm` telescoping (`KClean-cons`) and
  -- reduces to the single per-edge HEAD reconciliation `kfac-head`.
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
  -- ### `kfac-gen` — generalised K-side perm-tracking induction (mirror of
  -- `gblock-factor` tracking the K-prepend wrinkle):
  --   pe-termC (map ψK es) s ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf
  -- where the running stack `s` only `↭`s the clean `map injL P ++ map injR
  -- ys` form (via `pf`) and the codomain `↭`s the clean target (via `Br`).
  -- `Reservoir≤1` (the freshness side-condition) supplies the per-edge
  -- `Unique` of the running stack.

  -- ABBREVIATIONS shared by the helpers and `kfac-gen`.

  ys-step : (e : Fin K.nE) (ys : List (Fin K.nV)) → List (Fin K.nV)
  ys-step e ys = proj₁ (edge-step K ys e)

  -- The clean pure-R head.
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

  -- `Kterm` cons telescoping (mirror of `Lterm-cons`).  The pure-R run
  -- stays in `map injR _` form so the stack agreements are genuine `≡`s, no
  -- braid.  Generalise head stack / term / stack-emb so `zEqᵍ` matches refl.
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
  -- ### `kfac-gen` — the generalised K-side perm-tracking induction
  -- (K-mirror of `gblock-factor`).  Since K-edges PREPEND their `eout`,
  -- there is no clean stack `≡` to thread; we track the ACTUAL stack `s`
  -- with a perm `pf : s ↭ map injL P ++ map injR ys` to the clean form, and
  -- a perm `Br` from the clean target to the actual post-run stack:
  --   pe-termC (map ψK es) s ≈Term pvlC Br ∘ KClean es P ys ∘ pvlC pf.
  -- Head reconciled by `kfac-head`, tail by the IH, clean blocks merging via
  -- `KClean-cons`.  `Br` is shared with the IH definitionally (no keystone
  -- reconcile of the braid).

  -- The per-edge clean perm `pf1 : s1 ↭ map injL P ++ map injR (ys-step e
  -- ys)`, from `edge-step-↑ʳ-on-perm` transported onto `s1`.
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

  -- ### `kblock-factor` — K-side block factorization (the `s = clean,
  -- pf = ↭-refl, Br = ↭-sym KBraid` instance of `kfac-gen`; the codomain
  -- `coeC` and input perm both collapse to `id`).
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
-- ## The main assembly.  `decode-⊗-shape-inner` rests on two TERM-LEVEL
-- mixed-stack factorizations (term companions of the stack-only
-- `process-edges-↑ˡ-on-mixed` / `process-edges-↑ʳ-on-perm`):
--
--   * G-block (φ = injL): the G-edge run from the mixed dom factors as the
--     canonical G-run on `map injL G.dom` (relabelled to `decode f`)
--     tensored with `id` on the untouched `map injR K.dom`.
--   * K-block (φ = injR): the K-edge run factors as `id` on the
--     `map injL sG-final` prefix tensored with the canonical K-run
--     (relabelled to `decode g`).  K prepends its `eout` to the stack
--     front, so the post-K stack only `↭`s the disjoint target; that
--     reordering is absorbed into the final-permute by the keystone
--     `permute-via-vlab-≈Term-coherence-K`.
--
-- Each is a structural induction on the edge list with a per-edge box-of
-- suffix/prefix coherence reassociation; the final-permute recombination
-- into `decode f ⊗₁ decode g` is `BlockTensor.pvv-block-tensor`.
--------------------------------------------------------------------------------
-- ## The GENERIC ⊗ assembly — the decoder-agnostic core of
-- `decode-⊗-shape-inner`, abstracted over a "decoder interface" (the
-- sub-hypergraphs `G`/`K`, the decoder terms, their `Linear` + totality
-- witnesses, and the `domL`/`codL ≡ flatten` boundary equalities).  Both
-- the UNPRUNED and PRUNED decoders instantiate this (all interface
-- equations `refl`), so the assembly exists ONCE.
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
