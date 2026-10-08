{-# OPTIONS --safe --without-K #-}

-- Tensor decoder coherence via right-frame separability and a K-block braid.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; hTensor; module hTensor-impl; map-via)
open import Categories.APROP.Hypergraph.Model.Invariant sig
  using (inject+-inj; raise-inj)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefix.Properties
  using (extract-elem-↑ˡ-on-↑ʳ-list; extract-elem-↑ʳ-on-↑ˡ-list)
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig as SU
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig as DC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig as DSh
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig as PC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig
  using (module EquivStep)
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermRelabel sig using (pvv-≈̂)
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorReconcile sig as TR
open import Categories.Morphism.Reasoning SCat
open import Categories.Tactic.Category
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.All using (All; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Maybe using (nothing)
open Perm using (_↭_)

module KBlockDisjoint (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K using (injL; injR; ein-c-inj₁-red; ein-c-inj₂-red)
  open StrictDecoder (hTensor G K) using (vl; ein-disjoint; block-disjoint)

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  kblock-ein-disjoint
    : ∀ (eK : Fin K.nE) (P : List (Fin G.nV))
    → All (λ k → extract-elem k (map injL P) ≡ nothing) (C.ein (ψK eK))
  kblock-ein-disjoint eK P =
    subst (All (λ k → extract-elem k (map injL P) ≡ nothing))
          (sym (ein-c-inj₂-red eK))
          (map⁺ (universal (λ j → extract-elem-↑ʳ-on-↑ˡ-list G.nV j P) (K.ein eK)))

  gblock-ein-disjoint : ∀ (eG : Fin G.nE) (Q : List (Fin K.nV)) → ein-disjoint (ψG eG) (map injR Q)
  gblock-ein-disjoint eG Q =
    subst (All (λ k → extract-elem k (map injR Q) ≡ nothing))
          (sym (ein-c-inj₁-red eG))
          (map⁺ (universal (λ k → extract-elem-↑ˡ-on-↑ʳ-list k Q) (G.ein eG)))

  gblk : List (Fin C.nE)
  gblk = map (_↑ˡ K.nE) (allFin G.nE)

  gblock-disjoint : block-disjoint gblk (map injR K.dom)
  gblock-disjoint =
    map⁺ (universal (λ e → gblock-ein-disjoint e K.dom) (allFin G.nE))

module Embeds (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K public
    using ( injL; injR; vlab-injL; vlab-injR
          ; ein-c-inj₁-red; eout-c-inj₁-red; ein-c-inj₂-red; eout-c-inj₂-red
          ; elab-c-inj₁; elab-c-inj₂ )
  open KBlockDisjoint G K using (ψG; ψK)

  module TG = DC.EmbedGlue {H = G} {J = hTensor G K}
                injL (inject+-inj K.nV) vlab-injL
                ψG ein-c-inj₁-red eout-c-inj₁-red
                (map-via vlab-injL) elab-c-inj₁

  module TK = DC.EmbedGlue {H = K} {J = hTensor G K}
                injR (raise-inj G.nV) vlab-injR
                ψK ein-c-inj₂-red eout-c-inj₂-red
                (map-via vlab-injR) elab-c-inj₂

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
    open StrictDecoder ⟪ fg ⟫
      using (process-edgesˢ; vl; block-disjoint; stack-sepˢ; term-sepᵛ; rigidˢ)

    gblk kblk : List (Fin Hf.nE)
    gblk = map (_↑ˡ Kd.nE) (allFin Gd.nE)
    kblk = map (Gd.nE ↑ʳ_) (allFin Kd.nE)

    allFin≡ : allFin Hf.nE ≡ gblk ++ kblk
    allFin≡ = allFin-++ Gd.nE Kd.nE

    open DC.RunBlocks ⟪ fg ⟫
      using (absorbˢ; coeCod; run-split-atˢ; pe-stack-++ˢ)
    module KBD = KBlockDisjoint G K
    open Restrict (Fin Hf.nV) vl

    open Embeds G K using (injL; injR)

    g-disjoint : block-disjoint gblk (map injR Kd.dom)
    g-disjoint = KBD.gblock-disjoint

    Rsuf : List (Fin Hf.nV)
    Rsuf = map injR Kd.dom

    Lpre : List (Fin Hf.nV)
    Lpre = map injL Gd.dom

    Gon : HomV Lpre (proj₁ (process-edgesˢ gblk Lpre))
    Gon = proj₂ (process-edgesˢ gblk Lpre)

    sep : proj₁ (process-edgesˢ gblk Hf.dom)
          ≡ proj₁ (process-edgesˢ gblk Lpre) ++ Rsuf
    sep = stack-sepˢ gblk Lpre Rsuf g-disjoint

    gframe
      : proj₂ (process-edgesˢ gblk Hf.dom)
        ≈ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf})
    gframe = cast-flipᵛ refl sep (term-sepᵛ gblk Lpre Rsuf g-disjoint sep)

  private
    Krun : HomV (proj₁ (process-edgesˢ gblk Hf.dom))
                (proj₁ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom))))
    Krun = proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom)))

    stkSplit₀ : proj₁ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk Hf.dom)))
                ≡ RF.s-finˢ
    stkSplit₀ =
      sym (trans (cong (λ z → proj₁ (process-edgesˢ z Hf.dom)) allFin≡)
                 (pe-stack-++ˢ gblk kblk Hf.dom))

  KBlockσ : Set
  KBlockσ =
    Σ[ cand ∈ RF.s-finˢ ↭ Hf.cod ]
      ( RF.permuteˢ cand
          ∘ˢ coeCod stkSplit₀
               (Krun ∘ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf}))
        ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
            (decodePˢ f ⊗ˢ decodePˢ g) )

  braidˢ-from-kblock
    : KBlockσ → Σ[ cand ∈ RF.s-finˢ ↭ Hf.cod ] TR.Reconcile.BraidSigˢ f g cand
  braidˢ-from-kblock (cand , kb) =
    cand , ≈-trans (∘-resp ≈-refl split-eq) kb
    where
      split-eq
        : proj₂ (Run.runˢ ⟪ fg ⟫)
          ≈ˢ coeCod stkSplit₀
               (Krun ∘ᵛ castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf}))
      split-eq =
        ≈-trans (run-split-atˢ gblk kblk allFin≡ Hf.dom)
                (cast-resp refl (cong (map vl) stkSplit₀)
                           (∘-resp ≈-refl gframe))

  decodePˢ-⊗-cond : KBlockσ → decodePˢ fg ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
  decodePˢ-⊗-cond kb =
    let cand , braidˢ = braidˢ-from-kblock kb
    in TR.Reconcile.decodePˢ-⊗-from-braid f g cand braidˢ

  ----------------------------------------------------------------------
  -- K-block reconciliation
  ----------------------------------------------------------------------

  module Reconcile-e where
    private
      open PC.Kit ⟪ fg ⟫ using (⟦absorbʳ⟧)

      sG : List (Fin Hf.nV)
      sG = proj₁ (process-edgesˢ gblk Lpre)

      aG : List (Fin Hf.nV)
      aG = proj₁ (process-edgesˢ gblk Hf.dom)

      Kfin : List (Fin Hf.nV)
      Kfin = proj₁ (process-edgesˢ kblk Rsuf)

      Kclean : HomV Rsuf Kfin
      Kclean = proj₂ (process-edgesˢ kblk Rsuf)

      KCln : HomV (sG ++ Rsuf) (sG ++ Kfin)
      KCln = idᵛ {sG} ⊗ᵛ Kclean

      open DSh.Scr (Fin Hf.nV) Hf.vlab using (bswap)
      open EquivStep ⟪ fg ⟫
        using (process-edges-equivariantˢ; pvv-transˢ; pvv-inverse-leftˢ)

    module Gd' = Run G
    module Kd' = Run K

    s_G_final = Gd'.s-finˢ
    s_K_final = Kd'.s-finˢ

    sG≡ : sG ≡ map injL s_G_final
    sG≡ = Embeds.TG.proc-stack-embˢ G K (allFin Gd.nE) Gd.dom

    Kfin≡ : Kfin ≡ map injR s_K_final
    Kfin≡ = Embeds.TK.proc-stack-embˢ G K (allFin Kd.nE) Kd.dom

    Grun : HomS (map Gd.vlab Gd.dom) (map Gd.vlab s_G_final)
    Grun = proj₂ Gd'.runˢ

    Krun-K : HomS (map Kd.vlab Kd.dom) (map Kd.vlab s_K_final)
    Krun-K = proj₂ Kd'.runˢ

    pL : (map injL s_G_final) Perm.↭ (map injL Gd.cod)
    pL = PermProp.map⁺ injL (finalPermˢ f)

    pR : (map injR s_K_final) Perm.↭ (map injR Kd.cod)
    pR = PermProp.map⁺ injR (finalPermˢ g)

    combRaw : (map injL s_G_final ++ map injR s_K_final)
              Perm.↭ (map injL Gd.cod ++ map injR Kd.cod)
    combRaw = Perm.trans (PermProp.++⁺ʳ (map injR s_K_final) pL)
                         (PermProp.++⁺ˡ (map injL Gd.cod) pR)

    comb : (sG ++ Kfin) Perm.↭ Hf.cod
    comb = Perm.trans (Perm.↭-reflexive (cong₂ _++_ sG≡ Kfin≡)) combRaw

    Gon' : HomV (map injL Gd.dom) (map injL s_G_final)
    Gon' = castˢ refl (cong (map vl) sG≡) Gon

    Gc : HomS (map vl (map injL Gd.dom)) (map vl (map injL Gd.cod))
    Gc = RF.permuteˢ pL ∘ˢ Gon'

    decf-inner : HomS (map Gd.vlab Gd.dom) (map Gd.vlab Gd.cod)
    decf-inner = Gd'.permuteˢ (finalPermˢ f) ∘ˢ Grun

    Gc-≈̂ : Gc ≈̂ decf-inner
    Gc-≈̂ = ∘-resp-≈̂ Gperm-≈̂ Gon'-≈̂
      where
        Gperm-≈̂ : RF.permuteˢ pL ≈̂ Gd'.permuteˢ (finalPermˢ f)
        Gperm-≈̂ = pvv-≈̂ injL vl Gd.vlab (Embeds.vlab-injL G K) (finalPermˢ f)
        Gon'-≈̂ : Gon' ≈̂ Grun
        Gon'-≈̂ = ≈̂-trans cast-≈̂ (Embeds.TG.term-emb-≈̂ G K (allFin Gd.nE) Gd.dom)

    Kclean' : HomV (map injR Kd.dom) (map injR s_K_final)
    Kclean' = castˢ refl (cong (map vl) Kfin≡) Kclean

    Kc : HomS (map vl (map injR Kd.dom)) (map vl (map injR Kd.cod))
    Kc = RF.permuteˢ pR ∘ˢ Kclean'

    decg-inner : HomS (map Kd.vlab Kd.dom) (map Kd.vlab Kd.cod)
    decg-inner = Kd'.permuteˢ (finalPermˢ g) ∘ˢ Krun-K

    Kc-≈̂ : Kc ≈̂ decg-inner
    Kc-≈̂ = ∘-resp-≈̂ Kperm-≈̂ Kclean'-≈̂
      where
        Kperm-≈̂ : RF.permuteˢ pR ≈̂ Kd'.permuteˢ (finalPermˢ g)
        Kperm-≈̂ = pvv-≈̂ injR vl Kd.vlab (Embeds.vlab-injR G K) (finalPermˢ g)
        Kclean'-≈̂ : Kclean' ≈̂ Krun-K
        Kclean'-≈̂ = ≈̂-trans cast-≈̂ (Embeds.TK.term-emb-≈̂ G K (allFin Kd.nE) Kd.dom)

    target-≈̂
      : (RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR) ∘ˢ (Gon' ⊗ˢ Kclean')
        ≈̂ decodePˢ f ⊗ˢ decodePˢ g
    target-≈̂ =
      ≈̂-trans (≈ˢ⇒≈̂ interchangeˢ)
      (≈̂-trans (⊗-resp-≈̂ Gc-≈̂ Kc-≈̂)
               (≈̂-sym (⊗-resp-≈̂ (cast-≈̂ {p = ⟪⟫-domL f} {q = ⟪⟫-codL f})
                                (cast-≈̂ {p = ⟪⟫-domL g} {q = ⟪⟫-codL g}))))

    G-framed : HomV Hf.dom aG
    G-framed = castᵛ refl (sym sep) (Gon ⊗ᵛ idᵛ {Rsuf})

    pf₀ : aG Perm.↭ sG ++ Rsuf
    pf₀ = Perm.↭-reflexive sep

    private
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

    inner-frame : KCln ∘ᵛ (permuteᵛ pf₀ ∘ᵛ G-framed) ≈ᵛ Gon ⊗ᵛ Kclean
    inner-frame = inner-gen Gon Kclean sep

    comb-frame : RF.permuteˢ comb ≈̂ RF.permuteˢ pL ⊗ˢ RF.permuteˢ pR
    comb-frame =
      ≈̂-trans (⟦absorbʳ⟧ (cong₂ _++_ sG≡ Kfin≡))
      (≈̂-trans (∘-resp-≈̂ (RF.permuteˢ-frameˡ (map injL Gd.cod) pR)
                         (RF.permuteˢ-frame (map injR s_K_final) pL))
               (≈ˢ⇒≈̂ (≈-trans interchangeˢ (⊗-resp idˡ idʳ))))

    W-≈̂ : (Gon ⊗ᵛ Kclean) ≈̂ Gon' ⊗ˢ Kclean'
    W-≈̂ =
      ≈̂-trans (⊗ᵛ-≈̂ Gon Kclean)
              (⊗-resp-≈̂ (≈̂-sym (cast-≈̂ {p = refl} {q = cong (map vl) sG≡}))
                        (≈̂-sym (cast-≈̂ {p = refl} {q = cong (map vl) Kfin≡})))

    KBlockσ-from-factorization
      : (Br : (sG ++ Kfin) Perm.↭ proj₁ (process-edgesˢ kblk aG))
      → ( proj₂ (process-edgesˢ kblk aG)
          ≈ˢ RF.permuteˢ Br ∘ˢ (KCln ∘ˢ RF.permuteˢ pf₀) )
      → KBlockσ
    KBlockσ-from-factorization Br kfac =
      cand , goal
      where
        cand : RF.s-finˢ Perm.↭ Hf.cod
        cand = subst (Perm._↭ Hf.cod) stkSplit₀ (Perm.trans (Perm.↭-sym Br) comb)

        W : HomV Hf.dom (sG ++ Kfin)
        W = Gon ⊗ᵛ Kclean

        stepA : Krun ∘ᵛ G-framed ≈ᵛ RF.permuteˢ Br ∘ᵛ W
        stepA =
          ≈-trans (∘-resp kfac ≈-refl)
                  (pullʳ (≈-trans assocˢ inner-frame))

        candP≡ : subst (Perm._↭ Hf.cod) (sym stkSplit₀) cand
                 ≡ Perm.trans (Perm.↭-sym Br) comb
        candP≡ = subst-sym-subst stkSplit₀

        stepBC
          : RF.permuteˢ cand ∘ˢ coeCod stkSplit₀ (RF.permuteˢ Br ∘ˢ W)
            ≈ˢ RF.permuteˢ comb ∘ˢ W
        stepBC =
          ≈-trans (absorbˢ stkSplit₀ cand (RF.permuteˢ Br ∘ˢ W))
          (≈-trans (∘-resp (≡⇒≈ˢ (cong RF.permuteˢ candP≡)) ≈-refl)
          (≈-trans (∘-resp (pvv-transˢ (Perm.↭-sym Br) comb) ≈-refl)
                   (cancelInner (pvv-inverse-leftˢ Br))))

        stepD : RF.permuteˢ comb ∘ˢ W ≈̂ decodePˢ f ⊗ˢ decodePˢ g
        stepD = ≈̂-trans (∘-resp-≈̂ comb-frame W-≈̂) target-≈̂

        goal
          : RF.permuteˢ cand
              ∘ˢ coeCod stkSplit₀ (Krun ∘ᵛ G-framed)
            ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                (decodePˢ f ⊗ˢ decodePˢ g)
        goal =
          ≈-trans (∘-resp ≈-refl (cast-resp refl (cong (map vl) stkSplit₀) stepA))
          (≈-trans stepBC
            (viâ stepD ≈̂-refl
                 (cast-≈̂ {p = sym (⟪⟫-domL fg)} {q = sym (⟪⟫-codL fg)})))

    -- Swap the inert block to a suffix before using separability;
    -- left-frame separability fails (see `ExtractPrefix.Properties`).

    private
      disj-kblk : block-disjoint kblk sG
      disj-kblk =
        map⁺ (universal (λ e → subst (λ z → All (λ k → extract-elem k z ≡ nothing)
                                                (Hf.ein (Gd.nE ↑ʳ e)))
                                     (sym sG≡)
                                     (KBD.kblock-ein-disjoint e s_G_final))
                        (allFin Kd.nE))

      res-kblk : SUR.Reservoir≤1 ⟪ fg ⟫ kblk aG
      res-kblk =
        SUR.reservoir-split ⟪ fg ⟫ gblk kblk Hf.dom
          (subst (λ z → SUR.Reservoir≤1 ⟪ fg ⟫ z Hf.dom) allFin≡
            (SUR.dom-reservoir-prov ⟪ fg ⟫ (proj₂ (DAL.⟪⟫-LinearP fg))
              (allFin Hf.nE) Perm.↭-refl))

      ρ : aG Perm.↭ Rsuf ++ sG
      ρ = Perm.trans (Perm.↭-reflexive sep) (bswap sG Rsuf)

      equiv = process-edges-equivariantˢ kblk {s = Rsuf ++ sG} {s' = aG} ρ res-kblk

      ρf : proj₁ (process-edgesˢ kblk aG)
           Perm.↭ proj₁ (process-edgesˢ kblk (Rsuf ++ sG))
      ρf = proj₁ equiv

      sepK : proj₁ (process-edgesˢ kblk (Rsuf ++ sG)) ≡ Kfin ++ sG
      sepK = stack-sepˢ kblk Rsuf sG disj-kblk

      W' : HomV (Rsuf ++ sG) (Kfin ++ sG)
      W' = permuteᵛ (bswap sG Kfin) ∘ᵛ (KCln ∘ᵛ permuteᵛ (bswap Rsuf sG))

      mid-form
        : proj₂ (process-edgesˢ kblk (Rsuf ++ sG))
          ≈ᵛ castᵛ refl (sym sepK) W'
      mid-form =
        ≈-trans (cast-flipᵛ refl sepK (term-sepᵛ kblk Rsuf sG disj-kblk sepK))
          (cast-respᵛ refl (sym sepK)
            (≈-trans (box-conjᵛ Kclean sG)
              (∘-resp (≈-sym (BSC.block-swap-comm (Fin Hf.nV) Hf.vlab sG Kfin))
                      (∘-resp ≈-refl
                        (≈-sym (BSC.block-swap-comm (Fin Hf.nV) Hf.vlab
                                  Rsuf sG))))))

      perm-cast-absorb
        : ∀ {as s s' ys : List (Fin Hf.nV)}
            (eq : s ≡ s') (p : s' Perm.↭ ys) (T : HomV as s)
        → permuteᵛ p ∘ᵛ castᵛ refl eq T
          ≈ᵛ permuteᵛ (Perm.trans (Perm.↭-reflexive eq) p) ∘ᵛ T
      perm-cast-absorb refl p T = ≈-sym (∘-resp idʳ ≈-refl)

      Br' : (sG ++ Kfin) Perm.↭ proj₁ (process-edgesˢ kblk aG)
      Br' = Perm.trans (bswap sG Kfin)
              (Perm.trans (Perm.↭-reflexive (sym sepK)) (Perm.↭-sym ρf))

      pf' : aG Perm.↭ sG ++ Rsuf
      pf' = Perm.trans ρ (bswap Rsuf sG)

      pf-rigid : permuteᵛ pf' ≈ᵛ permuteᵛ pf₀
      pf-rigid =
        rigidˢ (SU.Unique-resp-↭ (Perm.↭-reflexive sep)
                 (SUR.Reservoir≤1⇒Unique ⟪ fg ⟫ kblk aG res-kblk))
               pf' pf₀

      regroup
        : ∀ {o1 o2 o3 o4 o5 o6 : List X}
            {H : HomS o5 o6} {O : HomS o4 o5} {M : HomS o3 o4}
            {I : HomS o2 o3} {P : HomS o1 o2}
        → (H ∘ˢ (O ∘ˢ (M ∘ˢ I))) ∘ˢ P
          ≈ˢ (H ∘ˢ O) ∘ˢ (M ∘ˢ (I ∘ˢ P))
      regroup = solve SCat

      kfac
        : proj₂ (process-edgesˢ kblk aG)
          ≈ᵛ permuteᵛ Br' ∘ᵛ (KCln ∘ᵛ permuteᵛ pf₀)
      kfac =
        ≈-trans (proj₂ equiv)
        (≈-trans (∘-resp ≈-refl (∘-resp mid-form ≈-refl))
        (≈-trans (≈-sym assocˢ)
        (≈-trans (∘-resp (perm-cast-absorb (sym sepK) (Perm.↭-sym ρf) W') ≈-refl)
        (≈-trans regroup
          (∘-resp ≈-refl (∘-resp ≈-refl pf-rigid))))))

    kblockσ : KBlockσ
    kblockσ = KBlockσ-from-factorization Br' kfac

decodePˢ-⊗-concrete
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
decodePˢ-⊗-concrete f g = Brd.decodePˢ-⊗-cond Brd.Reconcile-e.kblockσ
  where module Brd = Braid f g
