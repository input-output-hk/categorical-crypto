{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The K-BLOCK BRAID `braidˢ` of `Strict.TensorReconcile` — the LAST residual
-- of the strict ⊗-shape `decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g`.
--
-- `⟪ f ⊗₁ g ⟫ = hTensor ⟪f⟫ ⟪g⟫`, edges `range C.nE = gblk ++ kblk`
-- (`gblk = map (_↑ˡ K.nE)(range G.nE)`, `kblk = map (G.nE ↑ʳ_)(range K.nE)`),
-- boundary `map injL G.dom ++ map injR K.dom` / `… cod …`.
--
-- STRATEGY (mirror of the former non-strict `DecodeTensorShape` assembly tail, ~3800
-- LOC, but riding the proven strict substrate):
--
--   1. RUN-SPLIT.  `proj₂ runˢ` factors over `gblk ++ kblk` as
--      `(K-block run on after-G) ∘ˢ (G-block run on C.dom)` — PROVEN
--      `DecodeCompose.RunBlocks.pe-term-++ˢ`.
--   2. G-BLOCK FRAME.  The G-block run factors `(G-run on injL G.dom) ⊗ˢ
--      idˢ {map injR K.dom}` via the proven right-frame `term-sepˢ`
--      (`DecodeTensor.GBlock.G-block-frameˢ`); the G-run is bridged to
--      `decodePˢ f` through `TermEmbedˢ` at `φ = injL, ψ = _↑ˡ K.nE`.
--   3. K-BLOCK BRAID.  After G fires, the K-edge block acts on the `injR`
--      suffix but PREPENDS K's outputs in FRONT of `injL G.cod`, giving a
--      BRAIDED stack.  This is the genuine residual `kblock-braidˢ` below
--      (the strict twin of the non-strict `kblock-factor` + `box-braid`):
--      one clearly-typed `≈ˢ` stating the K-block run on the clean mixed
--      stack `map injL sG ++ map injR K.dom` factors as a `permuteˢ` braid
--      composed with `idˢ {injL sG} ⊗ˢ (K-run)`.  The K-run is bridged to
--      `decodePˢ g` through `TermEmbedˢ` at `φ = injR, ψ = G.nE ↑ʳ_`.
--   4. EQUIVARIANCE.  `process-edges-equivariantˢ` conjugates the K-block on
--      the actual `after-G` stack onto the canonical clean stack.
--   5. CANONICAL `cand` + FINAL RESORT.  `cand` is the assembled derivation;
--      `TensorReconcile.final-resortˢ` (`perm-rigidˢ`, `Unique` cod) closes
--      the loop with `finalPermˢ`.
--
-- WHAT IS GREEN HERE (postulate-free, `--safe --without-K`):
--   * `TG` / `TK` — the G-/K-side `TermEmbedˢ` instances, giving the two
--     block term-twins.
--   * `runˢ-factor` — the run-split + G-frame, as a single `≈ˢ`.
--   * the assembly `braidˢ-from-kblock` reducing `braidˢ` (hence the whole
--     ⊗-shape) to the single clearly-typed K-block residual `KBlockσ`.
--   * `decodePˢ-⊗-cond` — the ⊗-shape THEOREM, conditional on `KBlockσ`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using ( FlatGen; range; hTensor; module hTensor-impl
        ; map-via-inj; map-via-raise )
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.Morphism.Reasoning SCat using (pullʳ; cancelInner)
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
  using (module EquivStep; module TermEmbedˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig _≟X_ as DC
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorReconcile sig _≟X_ as TR
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig _≟X_ as PC
open import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock sig _≟X_
  using (module TKB4)
open import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorPVVRelabel sig _≟X_
  using (pvv-relabelˢ)

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## The two block embeddings.
--
-- These instantiate the proven strict `TermEmbedˢ` (the relabelling-
-- equivariance gate), giving each block run as a relabel of the matching
-- sub-decoder run.  The injectivity / label / endpoint fields all transfer
-- from `hTensor-impl`.

module Embeds (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K public
    using ( injL; injR; vlab-injL; vlab-injR
          ; ein-c-inj₁-red; eout-c-inj₁-red; ein-c-inj₂-red; eout-c-inj₂-red
          ; elab-c-inj₁; elab-c-inj₂ )

  ------------------------------------------------------------------------
  -- G-side embedding: φ = injL, ψ = _↑ˡ K.nE, H = G, J = hTensor G K.
  --
  -- `atom-ein`/`atom-eout`/`ψ-elab` are DERIVED from the raw endpoint
  -- reductions + edge-label reduction by `DC.EmbedGlue` (same builder
  -- `DecodeComposeAssembly` uses for the `hComposeP` twin).

  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  module GG = DC.EmbedGlue {H = G} {J = hTensor G K}
                injL ψG ein-c-inj₁-red eout-c-inj₁-red
                (map-via-inj vlab-injL) elab-c-inj₁

  module TG = TermEmbedˢ {H = G} {J = hTensor G K}
                injL (λ {x} {y} → ↑ˡ-injective K.nV x y)
                vlab-injL
                ψG ein-c-inj₁-red eout-c-inj₁-red
                GG.atom-ein GG.atom-eout GG.ψ-elab

  ------------------------------------------------------------------------
  -- K-side embedding: φ = injR, ψ = G.nE ↑ʳ_, H = K, J = hTensor G K.

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  module KG = DC.EmbedGlue {H = K} {J = hTensor G K}
                injR ψK ein-c-inj₂-red eout-c-inj₂-red
                (map-via-raise vlab-injR) elab-c-inj₂

  module TK = TermEmbedˢ {H = K} {J = hTensor G K}
                injR (λ {x} {y} → ↑ʳ-injective G.nV x y)
                vlab-injR
                ψK ein-c-inj₂-red eout-c-inj₂-red
                KG.atom-ein KG.atom-eout KG.ψ-elab

--------------------------------------------------------------------------------
-- ## The ⊗-shape, assembled from the K-block braid residual.
--
-- Threaded through the SAME deferred residual `permˢ-K` the whole strict
-- chain consumes (a `Support.PermK`, polymorphic over the vertex set), used
-- by `TensorReconcile.final-resortˢ` via `perm-rigidˢ`.

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) → Support.PermK V vlab)
  where

  module Braid {A B C D : ObjTerm}
    (f : HomTerm A B) (g : HomTerm C D)
    where
    private
      fg : HomTerm (A ⊗₀ C) (B ⊗₀ D)
      fg = f ⊗₁ g

      G K : Hypergraph FlatGen
      G = ⟪ f ⟫
      K = ⟪ g ⟫

      module Gd = Hypergraph G
      module Kd = Hypergraph K
      module RF = Run ⟪ fg ⟫
      module Hf = Hypergraph ⟪ fg ⟫
      open StrictDecoder ⟪ fg ⟫ using (process-edgesˢ; vl)

      open import Categories.APROP.Hypergraph.Model.Invariant sig using (range-++)

      gblk kblk : List (Fin Hf.nE)
      gblk = map (_↑ˡ Kd.nE) (range Gd.nE)
      kblk = map (Gd.nE ↑ʳ_) (range Kd.nE)

      -- `range Hf.nE ≡ gblk ++ kblk` (definitional split of the edge range).
      range≡ : range Hf.nE ≡ gblk ++ kblk
      range≡ = range-++ Gd.nE Kd.nE

      open DC.RunBlocks ⟪ fg ⟫
        using (absorbˢ; coeCod; run-split-atˢ; pe-stack-++ˢ)
      open StrictDecoder ⟪ fg ⟫
        using (block-disjoint; ein-disjoint; stack-sepˢ; term-sepᵛ)
      open Restrict (Fin Hf.nV) vl
        using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; castᵛ; _≈ᵛ_; permuteᵛ; cast-flipᵛ
              ; ⊗-respᵛ; interchangeᵛ )

      open import Data.Fin using (splitAt)
      open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
      import Data.Fin.Properties as FinP
      open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
      open import Data.Empty using (⊥; ⊥-elim)
      open import Relation.Nullary using (yes; no)
      open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (extract-elem)
      open Embeds G K using (injL; injR)

      -- `injL k ≢ injR j` (split lands in `inj₁` vs `inj₂`).
      injL≢injR : ∀ {k : Fin Gd.nV} {j : Fin Kd.nV} → injL k ≡ injR j → ⊥
      injL≢injR {k} {j} eq with trans (sym (splitAt-↑ˡ Gd.nV k Kd.nV))
                                (trans (cong (splitAt Gd.nV) eq)
                                       (splitAt-↑ʳ Gd.nV Kd.nV j))
      ... | ()

      injL∉injRs : ∀ (k : Fin Gd.nV) (ys : List (Fin Kd.nV))
                 → extract-elem (injL k) (map injR ys) ≡ nothing
      injL∉injRs k []       = refl
      injL∉injRs k (y ∷ ys) with injR y FinP.≟ injL k
      ... | yes p  = ⊥-elim (injL≢injR (sym p))
      ... | no  _  rewrite injL∉injRs k ys = refl

      -- The whole G-block's inputs are absent from the `injR` residual.
      g-disjoint : block-disjoint gblk (map injR Kd.dom)
      g-disjoint = all-gblk (range Gd.nE)
        where
          open Embeds G K using (ein-c-inj₁-red)
          all-injL : ∀ (ks : List (Fin Gd.nV))
                   → All (λ k → extract-elem k (map injR Kd.dom) ≡ nothing)
                         (map injL ks)
          all-injL []       = []ᴬ
          all-injL (k ∷ ks) = injL∉injRs k Kd.dom ∷ᴬ all-injL ks

          ein-disjointG : ∀ (eG : Fin Gd.nE) → ein-disjoint (eG ↑ˡ Kd.nE) (map injR Kd.dom)
          ein-disjointG eG =
            subst (λ ks → All (λ k → extract-elem k (map injR Kd.dom) ≡ nothing) ks)
                  (sym (ein-c-inj₁-red eG))
                  (all-injL (Gd.ein eG))

          all-gblk : ∀ (es : List (Fin Gd.nE))
                   → block-disjoint (map (_↑ˡ Kd.nE) es) (map injR Kd.dom)
          all-gblk []       = []ᴬ
          all-gblk (e ∷ es) = ein-disjointG e ∷ᴬ all-gblk es

      ------------------------------------------------------------------
      -- ## The G-block FRAME (the G-side core, via the proven RIGHT-frame
      -- `term-sepᵛ`).  `Hf.dom = Lpre ++ Rsuf` definitionally, so the G-block
      -- run factors as `Gon ⊗ᵛ idᵛ {Rsuf}` over the `List (Fin Hf.nV)` stack
      -- equality `sep`; no `map-++` endpoint is ever named.

      Rsuf : List (Fin Hf.nV)
      Rsuf = map injR Kd.dom

      Lpre : List (Fin Hf.nV)
      Lpre = map injL Gd.dom

      -- the G-block run on the pure-`injL` prefix.
      Gon : HomV Lpre (proj₁ (process-edgesˢ gblk Lpre))
      Gon = proj₂ (process-edgesˢ gblk Lpre)

      -- `aG ≡ sG ++ Rsuf` (definitional `Hf.dom = Lpre ++ Rsuf` + `stack-sepˢ`).
      sep : proj₁ (process-edgesˢ gblk Hf.dom)
            ≡ proj₁ (process-edgesˢ gblk Lpre) ++ Rsuf
      sep = stack-sepˢ gblk Lpre Rsuf g-disjoint

      -- the G-block run as a (back-)cast of the framed form.
      gframe
        : proj₂ (process-edgesˢ gblk Hf.dom)
          ≈ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf})
      gframe = cast-flipᵛ refl sep (term-sepᵛ gblk Lpre Rsuf g-disjoint sep)

      ------------------------------------------------------------------
      -- ## The G-block relabel bridge (via the proven `TG` embedding).
      -- `Gon` (the G-block run on the pure-`injL` prefix) relabels to the
      -- G SUB-decoder run `proj₂ (Run.runˢ G)`, modulo the `vlab-φ` boundary
      -- cast.  (`map ψG (range Gd.nE) = gblk`, `map injL Gd.dom = Lpre`.)
      Gon-bridge
        : (pCod : map Hf.vlab (proj₁ (process-edgesˢ gblk Lpre))
                  ≡ map Gd.vlab (proj₁ (StrictDecoder.process-edgesˢ G (range Gd.nE) Gd.dom)))
        → castˢ (Embeds.TG.vlab-φ G K Gd.dom) pCod Gon
          ≈ˢ proj₂ (Run.runˢ G)
      Gon-bridge pCod = Embeds.TG.process-edges-term-embˢ G K (range Gd.nE) Gd.dom pCod

      -- ## The K-block relabel bridge (via the proven `TK` embedding).
      -- The K-block C-run on the CANONICAL pure-`injR` stack `Rsuf = map injR
      -- Kd.dom` relabels to the K SUB-decoder run `proj₂ (Run.runˢ K)`,
      -- modulo the `vlab-φ` boundary cast.  (`map ψK (range Kd.nE) = kblk`.)
      -- This is the K-side companion the K-block braid `KBlockσ` consumes,
      -- after the equivariance conjugation onto the canonical stack.
      Kon-bridge
        : (pCod : map Hf.vlab (proj₁ (process-edgesˢ kblk Rsuf))
                  ≡ map Kd.vlab (proj₁ (StrictDecoder.process-edgesˢ K (range Kd.nE) Kd.dom)))
        → castˢ (Embeds.TK.vlab-φ G K Kd.dom) pCod
              (proj₂ (process-edgesˢ kblk Rsuf))
          ≈ˢ proj₂ (Run.runˢ K)
      Kon-bridge pCod = Embeds.TK.process-edges-term-embˢ G K (range Kd.nE) Kd.dom pCod

    ----------------------------------------------------------------------
    -- ## The K-BLOCK BRAID residual `KBlockσ`.
    --
    -- The strict, whole-run-level twin of `DecodeTensorShape`'s `Pcomp-eq`:
    -- with the run SPLIT over `gblk ++ kblk` (the K-block run on the post-G
    -- stack `after-G` precomposed with the G-block run on `Hf.dom`), there is
    -- a canonical re-sort derivation `cand : s-finˢ ↭ Hf.cod` such that the
    -- run-split inner term post-sorted by `cand` is the clean tensor at the
    -- boundary objects.  This packages: the K-block prepend braid (`σˢ` slide
    -- of the K-outputs back past `map injL G.cod`), the two block embeddings
    -- `TG`/`TK` (bridging the block runs to `decodePˢ f`/`decodePˢ g`), and
    -- the final collapse.  Cast-FREE at the boundary objects.
    -- the K-block run on the post-G stack.
    private
      Krun : HomV (proj₁ (process-edgesˢ gblk Hf.dom))
                  (proj₁ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom))))
      Krun = proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom)))

      stkSplit₀ : proj₁ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom)))
                  ≡ proj₁ (process-edgesˢ (range Hf.nE) Hf.dom)
      stkSplit₀ =
        trans (sym (pe-stack-++ˢ gblk kblk Hf.dom))
              (cong (λ z → proj₁ (process-edgesˢ z Hf.dom)) (sym range≡))

    KBlockσ : Set
    KBlockσ =
      Σ[ cand ∈ RF.s-finˢ ↭ Hf.cod ]
        ( RF.permuteˢ cand
            ∘ˢ coeCod stkSplit₀
                 (Krun ∘ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf}))
          ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
              (decodePˢ f ⊗ˢ decodePˢ g) )

    ----------------------------------------------------------------------
    -- ## `braidˢ` from `KBlockσ`.
    --
    -- Substituting the run-split `run-split-atˢ` (PROVEN) and the G-frame
    -- `gframe` (PROVEN, ⇐ `term-sepˢ`) into the C-run turns `KBlockσ` into
    -- exactly the `braidˢ` parameter of `TensorReconcile.reconcile-from-braid`
    -- for the chosen `cand`.  The narrowed `KBlockσ` now mentions only the
    -- K-block run and the FRAMED G-side `Gon ⊗ˢ idˢ`.

    braidˢ-from-kblock
      : KBlockσ
      → Σ[ cand ∈ RF.s-finˢ ↭ Hf.cod ]
          ( RF.permuteˢ cand ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
            ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                (decodePˢ f ⊗ˢ decodePˢ g) )
    braidˢ-from-kblock (cand , kb) =
      cand , ≈-trans (∘-resp ≈-refl split-eq) kb
      where
        -- `proj₂ runˢ ≈ castˢ refl (sym stkSplit) (Krun ∘ (G-framed))`.
        split-eq
          : proj₂ (Run.runˢ ⟪ fg ⟫)
            ≈ˢ coeCod stkSplit₀
                 (Krun ∘ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf}))
        split-eq =
          ≈-trans (run-split-atˢ gblk kblk range≡ Hf.dom)
                  (cast-resp refl (cong (map vl) stkSplit₀)
                             (∘-resp ≈-refl gframe))

    ----------------------------------------------------------------------
    -- ## The ⊗-shape, conditional on `KBlockσ`.

    decodePˢ-⊗-cond : KBlockσ → decodePˢ fg ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
    decodePˢ-⊗-cond kb =
      let cand , braidˢ = braidˢ-from-kblock kb
      in TR.Reconcile.decodePˢ-⊗-from-braid permˢ-K f g cand braidˢ

    ----------------------------------------------------------------------
    -- ## (e)-RECONCILE: `KBlockσ` from the K-block run factorization.
    --
    -- This is the LAST step.  `TKB6.kblock-factorize-res`, instantiated
    -- at the concrete K-block (`L = sG`, the G-output block; `s = aG`, the
    -- post-G stack; `s_R = Rsuf`, the canonical pure-`injR` K-stack), supplies
    -- the K-prepend braid + clean factorization
    --     Krun ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ kblk sG Rsuf ∘ˢ permuteˢ pf).
    -- We reconcile this to `KBlockσ` by: collapsing the G-frame against the
    -- clean K-head via `interchangeˢ` (giving `Gon ⊗ Kclean`), bridging `Gon`
    -- ↦ `decodePˢ f`-core / `Kclean` ↦ `decodePˢ g`-core via `TG`/`TK`, and
    -- absorbing `Br`, `pf`, and the two sub-final-permutes into the single
    -- `cand` by `perm-rigidˢ` on the `Unique` cod (`Linear⇒cod-Unique`).
    ----------------------------------------------------------------------

    module Reconcile-e where
      private
        -- the `Fin Hf.nV` Kelly instance (the same one `TensorReconcile` /
        -- `kblock-factorize-res` thread).
        open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
        permˢ-K-fg : Support.PermK (Fin Hf.nV) Hf.vlab
        permˢ-K-fg = permˢ-K (Fin Hf.nV) _≟F_ Hf.vlab

        -- the wiring-groupoid calculus at `⟪ fg ⟫` (the `≈̂`-level frames).
        open PC.Kit ⟪ fg ⟫ permˢ-K-fg using (⟦absorbʳ⟧; ⟦frameˡ⟧; ⟦frameʳ⟧)

        -- the G-output block (all `injL`), and the post-G stack `aG`.
        sG : List (Fin Hf.nV)
        sG = proj₁ (process-edgesˢ gblk Lpre)

        aG : List (Fin Hf.nV)
        aG = proj₁ (process-edgesˢ gblk Hf.dom)

        -- the canonical clean K-run on `Rsuf`.
        Kfin : List (Fin Hf.nV)
        Kfin = proj₁ (process-edgesˢ kblk Rsuf)

        Kclean : HomV Rsuf Kfin
        Kclean = proj₂ (process-edgesˢ kblk Rsuf)

        -- the clean K-block frame `idˢ {m sG} ⊗ Kclean`, `map-++`-cast-framed
        -- (DEFINITIONALLY `TKB4.KCleanˢ ⟪fg⟫ permˢ-K-fg kblk sG Rsuf`).
        KCln : HomV (sG ++ Rsuf) (sG ++ Kfin)
        KCln = TKB4.KCleanˢ ⟪ fg ⟫ permˢ-K-fg kblk sG Rsuf

      -- PUBLIC re-exports (so the new file `TensorKBlockFinal` can state the
      -- `Br` / `KFAC` it feeds in, mirroring the private bindings).
      sGᴾ aGᴾ Kfinᴾ : List (Fin Hf.nV)
      sGᴾ   = sG
      aGᴾ   = aG
      Kfinᴾ = Kfin

      KClnᴾ : HomS (map vl (sGᴾ ++ Rsuf)) (map vl (sGᴾ ++ Kfinᴾ))
      KClnᴾ = KCln

      ------------------------------------------------------------------
      -- ### Foundational stack / boundary identities.

      module Gd' = Run G
      module Kd' = Run K

      s_G_final : List (Fin Gd.nV)
      s_G_final = proj₁ (Gd'.process-edgesˢ (range Gd.nE) Gd.dom)

      s_K_final : List (Fin Kd.nV)
      s_K_final = proj₁ (Kd'.process-edgesˢ (range Kd.nE) Kd.dom)

      -- `sG ≡ map injL s_G_final` (G-block stack-emb, via `TG.proc-stack-embˢ`).
      sG≡ : sG ≡ map injL s_G_final
      sG≡ = Embeds.TG.proc-stack-embˢ G K (range Gd.nE) Gd.dom

      -- `Kfin ≡ map injR s_K_final` (K-block stack-emb, via `TK.proc-stack-embˢ`).
      Kfin≡ : Kfin ≡ map injR s_K_final
      Kfin≡ = Embeds.TK.proc-stack-embˢ G K (range Kd.nE) Kd.dom

      ------------------------------------------------------------------
      -- ### The G-/K-block run bridges (instantiated `Gon-bridge`/`Kon-bridge`).

      -- the sub-decoder runs (G/K).
      Grun : HomS (map Gd.vlab Gd.dom) (map Gd.vlab s_G_final)
      Grun = proj₂ (Run.runˢ G)

      Krun-K : HomS (map Kd.vlab Kd.dom) (map Kd.vlab s_K_final)
      Krun-K = proj₂ (Run.runˢ K)

      -- the `pCod` boundary proofs.
      pCodG : map vl sG ≡ map Gd.vlab s_G_final
      pCodG = trans (cong (map vl) sG≡) (Embeds.TG.vlab-φ G K s_G_final)

      pCodK : map vl Kfin ≡ map Kd.vlab s_K_final
      pCodK = trans (cong (map vl) Kfin≡) (Embeds.TK.vlab-φ G K s_K_final)

      -- `Gon` relabels to `Grun` (boundary `vlab-φ`).
      Gbridge : castˢ (Embeds.TG.vlab-φ G K Gd.dom) pCodG Gon ≈ˢ Grun
      Gbridge = Gon-bridge pCodG

      -- `Kclean` relabels to `Krun-K` (boundary `vlab-φ`).  `Kon-bridge` is on
      -- `proj₂ (process-edgesˢ kblk Rsuf)` = `Kclean`.
      Kbridge : castˢ (Embeds.TK.vlab-φ G K Kd.dom) pCodK Kclean ≈ˢ Krun-K
      Kbridge = Kon-bridge pCodK

      ------------------------------------------------------------------
      -- ### The two sub-final-permutes, relabelled to the C-level.


      -- the injL-/injR-lifted sub-final permutes, on `Fin Hf.nV`.
      pL : (map injL s_G_final) Perm.↭ (map injL Gd.cod)
      pL = PermProp.map⁺ injL (finalPermˢ f)

      pR : (map injR s_K_final) Perm.↭ (map injR Kd.cod)
      pR = PermProp.map⁺ injR (finalPermˢ g)

      -- the combined boundary derivation `(sG ++ Kfin) ↭ Hf.cod`, built from the
      -- two lifted sub-permutes (subst the endpoints by `sG≡`/`Kfin≡`).
      combRaw : (map injL s_G_final ++ map injR s_K_final)
                Perm.↭ (map injL Gd.cod ++ map injR Kd.cod)
      combRaw = Perm.trans (PermProp.++⁺ʳ (map injR s_K_final) pL)
                           (PermProp.++⁺ˡ (map injL Gd.cod) pR)

      comb : (sG ++ Kfin) Perm.↭ Hf.cod
      comb = Perm.trans (Perm.↭-reflexive (cong₂ _++_ sG≡ Kfin≡)) combRaw

      ------------------------------------------------------------------
      -- ### G-/K-part C-level twins (`decodePˢ f`/`g`-cores under relabel).

      φGdom = Embeds.TG.vlab-φ G K Gd.dom
      φGcod = Embeds.TG.vlab-φ G K Gd.cod
      φGsf  = Embeds.TG.vlab-φ G K s_G_final
      φKdom = Embeds.TK.vlab-φ G K Kd.dom
      φKcod = Embeds.TK.vlab-φ G K Kd.cod
      φKsf  = Embeds.TK.vlab-φ G K s_K_final

      -- G-side `sG≡`-corrected G-run, and the C-level G-part `permuteˢ pL ∘ Gon'`.
      Gon' : HomV (map injL Gd.dom) (map injL s_G_final)
      Gon' = castˢ refl (cong (map vl) sG≡) Gon

      Gc : HomS (map vl (map injL Gd.dom)) (map vl (map injL Gd.cod))
      Gc = RF.permuteˢ pL ∘ˢ Gon'

      -- the G sub-decoder INNER (`permuteˢ (finalPermˢ f) ∘ Grun`).
      decf-inner : HomS (map Gd.vlab Gd.dom) (map Gd.vlab Gd.cod)
      decf-inner = Gd'.permuteˢ (finalPermˢ f) ∘ˢ Grun

      -- G-part permute relabel: `castˢ φGsf φGcod (permuteˢ pL) ≈ permuteˢ_G fpf`.
      Gperm-relabel : castˢ φGsf φGcod (RF.permuteˢ pL) ≈ˢ Gd'.permuteˢ (finalPermˢ f)
      Gperm-relabel =
        ≈-trans (≡⇒≈ˢ (cast-irrel φGsf PGd φGcod PGc (RF.permuteˢ pL)))
                (pvv-relabelˢ injL vl Gd.vlab (Embeds.vlab-injL G K)
                   (finalPermˢ f) PGd PGc)
        where
          PGd : map vl (map injL s_G_final) ≡ map Gd.vlab s_G_final
          PGd = φGsf
          PGc : map vl (map injL Gd.cod) ≡ map Gd.vlab Gd.cod
          PGc = φGcod

      -- G-part twin: `castˢ φGdom φGcod Gc ≈ decf-inner`.
      Gc-twin : castˢ φGdom φGcod Gc ≈ˢ decf-inner
      Gc-twin =
        ≈-trans (∘-cast-split φGdom φGsf φGcod (RF.permuteˢ pL) Gon')
                (∘-resp Gperm-relabel Gon'-bridge)
        where
          -- `castˢ φGdom φGsf Gon' ≈ Grun` (fuse the `sG≡` cast into `Gbridge`).
          Gon'-bridge : castˢ φGdom φGsf Gon' ≈ˢ Grun
          Gon'-bridge =
            ≈-trans (≡⇒≈ˢ (cast-fuse refl φGdom (cong (map vl) sG≡) φGsf Gon))
            (≈-trans (≡⇒≈ˢ (cast-irrel (trans refl φGdom) φGdom
                              (trans (cong (map vl) sG≡) φGsf) pCodG Gon))
                     Gbridge)

      -- K-side `Kfin≡`-corrected clean K-run, and the C-level K-part.
      Kclean' : HomV (map injR Kd.dom) (map injR s_K_final)
      Kclean' = castˢ refl (cong (map vl) Kfin≡) Kclean

      Kc : HomS (map vl (map injR Kd.dom)) (map vl (map injR Kd.cod))
      Kc = RF.permuteˢ pR ∘ˢ Kclean'

      decg-inner : HomS (map Kd.vlab Kd.dom) (map Kd.vlab Kd.cod)
      decg-inner = Kd'.permuteˢ (finalPermˢ g) ∘ˢ Krun-K

      Kperm-relabel : castˢ φKsf φKcod (RF.permuteˢ pR) ≈ˢ Kd'.permuteˢ (finalPermˢ g)
      Kperm-relabel =
        ≈-trans (≡⇒≈ˢ (cast-irrel φKsf PKd φKcod PKc (RF.permuteˢ pR)))
                (pvv-relabelˢ injR vl Kd.vlab (Embeds.vlab-injR G K)
                   (finalPermˢ g) PKd PKc)
        where
          PKd : map vl (map injR s_K_final) ≡ map Kd.vlab s_K_final
          PKd = φKsf
          PKc : map vl (map injR Kd.cod) ≡ map Kd.vlab Kd.cod
          PKc = φKcod

      Kc-twin : castˢ φKdom φKcod Kc ≈ˢ decg-inner
      Kc-twin =
        ≈-trans (∘-cast-split φKdom φKsf φKcod (RF.permuteˢ pR) Kclean')
                (∘-resp Kperm-relabel Kclean'-bridge)
        where
          Kclean'-bridge : castˢ φKdom φKsf Kclean' ≈ˢ Krun-K
          Kclean'-bridge =
            ≈-trans (≡⇒≈ˢ (cast-fuse refl φKdom (cong (map vl) Kfin≡) φKsf Kclean))
            (≈-trans (≡⇒≈ˢ (cast-irrel (trans refl φKdom) φKdom
                              (trans (cong (map vl) Kfin≡) φKsf) pCodK Kclean))
                     Kbridge)

      ------------------------------------------------------------------
      -- ### `permuteˢ combRaw` frame-decomposition.
      --
      -- `permuteˢ combRaw ≈̂ RF.permuteˢ pL ⊗ RF.permuteˢ pR`, read off the
      -- `PermCalc` frames: `⟦trans⟧` is definitional, `⟦frameʳ⟧`/`⟦frameˡ⟧`
      -- present the two framed factors heterogeneously (so no intermediate
      -- `map-++` endpoint is ever named) and `interchangeˢ` merges them.

      combRaw-frame
        : RF.permuteˢ combRaw ≈̂ RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR
      combRaw-frame =
        ≈̂-trans (∘-resp-≈̂ (⟦frameˡ⟧ (map injL Gd.cod) pR)
                          (⟦frameʳ⟧ (map injR s_K_final) pL))
                (≈ˢ⇒≈̂ (≈-trans interchangeˢ (⊗-resp idˡ idʳ)))

      ------------------------------------------------------------------
      -- ### `Gc ⊗ Kc` decomposition 1: to the sub-decoder cores.
      --
      -- `cast-⊗-both` (the two-sided cast pull-out across `⊗`) is now the kit
      -- combinator from `FreeStrictSMC`; it splits `cast (h ⊗ k)`, so the
      -- fuse direction used here is its `sym`.

      GcKc→dec
        : Gc ⊗ˢ Kc
          ≈ˢ castˢ (cong₂ _++_ (sym φGdom) (sym φKdom))
                   (cong₂ _++_ (sym φGcod) (sym φKcod))
              (decf-inner ⊗ˢ decg-inner)
      GcKc→dec =
        ≈-trans (⊗-resp (cast-flip φGdom φGcod Gc-twin)
                        (cast-flip φKdom φKcod Kc-twin))
                (≡⇒≈ˢ (sym (cast-⊗-both (sym φGdom) (sym φGcod) (sym φKdom) (sym φKcod)
                             decf-inner decg-inner)))

      ------------------------------------------------------------------
      -- ### `Gc ⊗ Kc` decomposition 2: to `permuteˢ comb ∘ (Gon ⊗ Kclean)`.

      GcKc→comb : Gc ⊗ˢ Kc ≈ˢ (RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean')
      GcKc→comb = ≈-sym interchangeˢ

      ------------------------------------------------------------------
      -- ### The boundary tensor as a cast of `decf-inner ⊗ decg-inner`.

      private
        Df = ⟪⟫-domL f
        Cf = ⟪⟫-codL f
        Dg = ⟪⟫-domL g
        Cg = ⟪⟫-codL g

      -- `decodePˢ f ⊗ decodePˢ g ≡ castₜ (decf-inner ⊗ decg-inner)` (definitional
      -- `decodePˢ` + `cast-⊗-both`).
      decT-cast
        : decodePˢ f ⊗ˢ decodePˢ g
          ≡ castˢ (cong₂ _++_ Df Dg) (cong₂ _++_ Cf Cg)
              (decf-inner ⊗ˢ decg-inner)
      decT-cast = sym (cast-⊗-both Df Cf Dg Cg decf-inner decg-inner)

      ------------------------------------------------------------------
      -- ### TARGET equation: the C-level `(pL⊗pR) ∘ (Gon'⊗Kclean')` equals the
      -- boundary tensor, modulo the explicit boundary casts `Bd⁻`/`Bc⁻`.

      Bd⁻ = cong₂ _++_ (trans φGdom Df) (trans φKdom Dg)
      Bc⁻ = cong₂ _++_ (trans φGcod Cf) (trans φKcod Cg)

      target-core
        : castˢ Bd⁻ Bc⁻ ((RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean'))
          ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
      target-core =
        ≈-trans (cast-resp Bd⁻ Bc⁻ (≈-trans (≈-sym GcKc→comb) GcKc→dec))
        -- castˢ Bd⁻ Bc⁻ (castₚ (decf-inner ⊗ decg-inner))
        (≈-trans
          (≡⇒≈ˢ
            (trans (cast-fuse (cong₂ _++_ (sym φGdom) (sym φKdom)) Bd⁻
                      (cong₂ _++_ (sym φGcod) (sym φKcod)) Bc⁻
                      (decf-inner ⊗ˢ decg-inner))
                   (cast-irrel
                     (trans (cong₂ _++_ (sym φGdom) (sym φKdom)) Bd⁻)
                     (cong₂ _++_ Df Dg)
                     (trans (cong₂ _++_ (sym φGcod) (sym φKcod)) Bc⁻)
                     (cong₂ _++_ Cf Cg)
                     (decf-inner ⊗ˢ decg-inner))))
          (≡⇒≈ˢ (sym decT-cast)))

      ------------------------------------------------------------------
      -- ### The G-framed factor (matching `KBlockσ`'s body), and the inner
      -- interchange `KCln ∘ (permuteˢ pf₀ ∘ G-framed) ≈ castₓ (Gon' ⊗ Kclean')`.

      G-framed : HomV Hf.dom aG
      G-framed = castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf})

      pf₀ : aG Perm.↭ sG ++ Rsuf
      pf₀ = Perm.↭-reflexive sep

      private
        -- A clean generic interchange, matched on the `sep` stack equality so
        -- the `permuteᵛ pf₀` collapses to `idᵛ` and the `castᵛ` vanishes;
        -- leaves the bare `interchangeᵛ`.
        inner-gen
          : ∀ {sGx Kfinx aGx : List (Fin Hf.nV)}
              (Gonx : HomV Lpre sGx) (Kcleanx : HomV Rsuf Kfinx)
              (sepe : aGx ≡ sGx ++ Rsuf)
          → (idᵛ {sGx} ⊗ᵛ Kcleanx)
              ∘ᵛ (permuteᵛ (Perm.↭-reflexive sepe)
                    ∘ᵛ castᵛ refl (sym sepe) (Gonx ⊗ᵛ idᵛ {Rsuf}))
            ≈ᵛ Gonx ⊗ᵛ Kcleanx
        inner-gen Gonx Kcleanx refl =
          ≈-trans (∘-resp ≈-refl idˡ)
                  (≈-trans interchangeᵛ (⊗-respᵛ idˡ idʳ))

      -- the inner interchange, producing the C-level `Gon ⊗ᵛ Kclean`.
      inner-frame : KCln ∘ᵛ (permuteᵛ pf₀ ∘ᵛ G-framed) ≈ᵛ Gon ⊗ᵛ Kclean
      inner-frame = inner-gen Gon Kclean sep

      ------------------------------------------------------------------
      -- ### `permuteˢ comb` frame: to `castˢ … (permuteˢ pL ⊗ permuteˢ pR)`.
      --
      -- `comb`'s reindexing factor is absorbed inside `permuteˢ` (`⟦absorbʳ⟧`),
      -- so no `subst₂`-of-derivation bridge is needed.

      private
        mLsf = map-++ vl (map injL s_G_final) (map injR s_K_final)
        mLcc = map-++ vl (map injL Gd.cod) (map injR Kd.cod)

        combDom : map vl (map injL s_G_final) ++ map vl (map injR s_K_final)
                  ≡ map vl (sG ++ Kfin)
        combDom = trans (sym mLsf) (cong (map vl) (sym (cong₂ _++_ sG≡ Kfin≡)))

      comb-frame
        : RF.permuteˢ comb
          ≈ˢ castˢ combDom (sym mLcc) (RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR)
      comb-frame =
        ≈̂⇒≈ˢ (≈̂-trans (⟦absorbʳ⟧ (cong₂ _++_ sG≡ Kfin≡))
              (≈̂-trans combRaw-frame
                       (≈̂-sym (cast-≈̂ {p = combDom} {q = sym mLcc}))))

      private
        -- `Gon ⊗ᵛ Kclean ≈ castₚ (Gon' ⊗ˢ Kclean')` (push the `sG≡`/`Kfin≡`
        -- casts in), matched on `sG≡`/`Kfin≡` so `Gon'`/`Kclean'` collapse to
        -- `Gon`/`Kclean` and the two `⊗ᵛ` casts differ only by UIP.
        GK-gen
          : ∀ {sGx Kfinx : List (Fin Hf.nV)}
              (Gonx : HomV Lpre sGx) (Kcleanx : HomV Rsuf Kfinx)
              (sGe : sGx ≡ map injL s_G_final) (Kfe : Kfinx ≡ map injR s_K_final)
              (Q : map vl (map injL s_G_final) ++ map vl (map injR s_K_final)
                   ≡ map vl (sGx ++ Kfinx))
          → Gonx ⊗ᵛ Kcleanx
            ≈ᵛ castˢ (sym (map-++ vl Lpre Rsuf)) Q
                (castˢ refl (cong (map vl) sGe) Gonx
                  ⊗ˢ castˢ refl (cong (map vl) Kfe) Kcleanx)
        GK-gen {sGx} {Kfinx} Gonx Kcleanx refl refl Q =
          ≡⇒≈ˢ (cast-irrel (sym (map-++ vl Lpre Rsuf)) (sym (map-++ vl Lpre Rsuf))
                  (sym (map-++ vl sGx Kfinx)) Q (Gonx ⊗ˢ Kcleanx))

      ----------------------------------------------------------------
      -- ## THE (e)-RECONCILE: `KBlockσ` from the K-block factorization.
      --
      -- Given the K-block factorization at the chosen reflexive `pf₀` and ANY
      -- braid `Br`, build `cand` (absorbing `Br`, `pf₀`, and the two sub-final
      -- permutes) and discharge the `KBlockσ` equation.

      KBlockσ-from-factorization
        : (Br : (sG ++ Kfin) Perm.↭ proj₁ (process-edgesˢ kblk aG))
        → ( proj₂ (process-edgesˢ kblk aG)
            ≈ˢ RF.permuteˢ Br ∘ˢ (KCln ∘ˢ RF.permuteˢ pf₀) )
        → KBlockσ
      KBlockσ-from-factorization Br kfac =
        cand , goal
        where
          open EquivStep ⟪ fg ⟫ using (pvv-transˢ; pvv-inverse-leftˢ)

          cand : RF.s-finˢ Perm.↭ Hf.cod
          cand = subst (Perm._↭ Hf.cod) stkSplit₀ (Perm.trans (Perm.↭-sym Br) comb)

          -- the inner W = `Gon ⊗ᵛ Kclean` (from `inner-frame`).
          W : HomV Hf.dom (sG ++ Kfin)
          W = Gon ⊗ᵛ Kclean

          -- Step A: `Krun ∘ G-framed ≈ permuteˢ Br ∘ W`.
          stepA : Krun ∘ᵛ G-framed ≈ᵛ RF.permuteˢ Br ∘ᵛ W
          stepA =
            ≈-trans (∘-resp kfac ≈-refl)
                    (pullʳ (≈-trans assocˢ inner-frame))

          candP≡ : subst (Perm._↭ Hf.cod) (sym stkSplit₀) cand
                   ≡ Perm.trans (Perm.↭-sym Br) comb
          candP≡ = subst-sym-subst stkSplit₀
            where
              open import Relation.Binary.PropositionalEquality using (subst-sym-subst)

          -- Step B/C: absorb `coeCod stkSplit₀` + cancel `Br`.
          stepBC
            : RF.permuteˢ cand ∘ˢ coeCod stkSplit₀ (RF.permuteˢ Br ∘ˢ W)
              ≈ˢ RF.permuteˢ comb ∘ˢ W
          stepBC =
            ≈-trans (absorbˢ stkSplit₀ cand (RF.permuteˢ Br ∘ˢ W))
            (≈-trans (∘-resp (≡⇒≈ˢ (cong RF.permuteˢ candP≡)) ≈-refl)
            (≈-trans (∘-resp (pvv-transˢ (Perm.↭-sym Br) comb) ≈-refl)
                     (cancelInner (pvv-inverse-leftˢ Br))))

          WQ : map vl (map injL s_G_final) ++ map vl (map injR s_K_final)
               ≡ map vl (sG ++ Kfin)
          WQ = trans (sym (cong₂ _++_ (cong (map vl) sG≡) (cong (map vl) Kfin≡)))
                     (sym (map-++ vl sG Kfin))

          W-primed : W ≈ˢ castˢ (sym (map-++ vl Lpre Rsuf)) WQ (Gon' ⊗ˢ Kclean')
          W-primed = GK-gen Gon Kclean sG≡ Kfin≡ WQ

          -- Step D: `permuteˢ comb ∘ W ≈ castˢ (sym mLR)(sym mLcc)
          --            ((pL⊗pR) ∘ (Gon'⊗Kclean'))`.
          stepD
            : RF.permuteˢ comb ∘ˢ W
              ≈ˢ castˢ (sym (map-++ vl Lpre Rsuf)) (sym mLcc)
                  ((RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean'))
          stepD =
            ≈-trans (∘-resp comb-frame W-primed)
            -- castₐ(pL⊗pR) ∘ castᵦ(Gon'⊗Kclean')  →  align mid (cast-irrel) + split
            (≈-trans
              (∘-resp
                (≡⇒≈ˢ (cast-irrel combDom WQ (sym mLcc) (sym mLcc)
                         (RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR)))
                ≈-refl)
              (≈-sym (∘-cast-split (sym (map-++ vl Lpre Rsuf)) WQ
                       (sym mLcc)
                       (RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) (Gon' ⊗ˢ Kclean'))))

          -- Step E (target-final): bridge to the boundary tensor via `target-core`.
          target-final
            : castˢ (sym (map-++ vl Lpre Rsuf)) (sym mLcc)
                ((RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean'))
              ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                  (decodePˢ f ⊗ˢ decodePˢ g)
          target-final =
            ≈-trans
              (≡⇒≈ˢ (cast-irrel (sym (map-++ vl Lpre Rsuf))
                       (trans Bd⁻ (sym (⟪⟫-domL fg)))
                       (sym mLcc) (trans Bc⁻ (sym (⟪⟫-codL fg)))
                       ((RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean'))))
            (≈-trans
              (≡⇒≈ˢ (sym (cast-fuse Bd⁻ (sym (⟪⟫-domL fg)) Bc⁻ (sym (⟪⟫-codL fg))
                          ((RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean')))))
              (cast-resp (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg)) target-core))

          goal
            : RF.permuteˢ cand
                ∘ˢ coeCod stkSplit₀ (Krun ∘ᵛ G-framed)
              ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                  (decodePˢ f ⊗ˢ decodePˢ g)
          goal =
            ≈-trans (∘-resp ≈-refl (cast-resp refl (cong (map vl) stkSplit₀) stepA))
            (≈-trans stepBC (≈-trans stepD target-final))

      -- PUBLIC re-export of the chosen reflexive `pf₀`.
      pf₀ᴾ : aGᴾ Perm.↭ sGᴾ ++ Rsuf
      pf₀ᴾ = pf₀
