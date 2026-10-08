{-# OPTIONS --safe --without-K #-}

-- Isomorphism transport followed by order invariance identifies decodings.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoTransport
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)

import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Model.Dependency using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫; dep-irrefl-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig using (Linear⇒cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig using (module Run)
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig as DC2
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig as PC
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig as SS

open import Data.Fin.Base using (Fin)
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Function using (Injective)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Nullary using (¬_)

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             (run-interchange : SS.PerHG.RunInterchangeAt H dih lin) where
  open SS.PerHG H dih lin
    using (Order; Validˢ; decodeOrdˢ; _↝_; _↝*_; NoInv; connectivity
          ; swap-step; swap-validityˢ)

  swap-≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
          → o₁ Perm.↭ allFin (Hypergraph.nE H)
          → (p₁ : Validˢ o₁) (p₂ : Validˢ o₂)
          → decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  swap-≈ˢ = SS.swap-≈ˢ H dih lin run-interchange

  ↝⇒↭ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → o₁ Perm.↭ o₂
  ↝⇒↭ (swap-step ps {x} {y} qs _) = PermProp.++⁺ˡ ps (Perm.swap x y Perm.refl)

  ↝*⇒≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂
        → o₁ Perm.↭ allFin (Hypergraph.nE H)
        → (p₁ : Validˢ o₁)
        → Σ[ p₂ ∈ Validˢ o₂ ] decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  ↝*⇒≈ˢ ε        o₁↭range p₁ = p₁ , ≈-refl
  ↝*⇒≈ˢ (s ◅ ss) o₁↭range p₁ =
    let p-mid          = swap-validityˢ s p₁
        o-mid↭range    = Perm.↭-trans (Perm.↭-sym (↝⇒↭ s)) o₁↭range
        (p₂ , mid≈rec) = ↝*⇒≈ˢ ss o-mid↭range p-mid
    in  p₂ , ≈-trans (swap-≈ˢ s o₁↭range p₁ p-mid) mid≈rec

  -- Choosing the natural target order lets one permutation witness supply
  -- both connectivity and the swap-step provenance.
  order-invariantˢ :
    ∀ (o₁ : Order) → o₁ Perm.↭ allFin (Hypergraph.nE H) →
    NoInv o₁ → NoInv (allFin (Hypergraph.nE H)) →
    (p₁ : Validˢ o₁) →
    Σ[ p₂ ∈ Validˢ (allFin (Hypergraph.nE H)) ]
      decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ (allFin (Hypergraph.nE H)) p₂
  order-invariantˢ o₁ p n₁ n₂ p₁ = ↝*⇒≈ˢ (connectivity p n₁ n₂) p p₁

module _ {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
         (run-interchange-H
           : SS.PerHG.RunInterchangeAt ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f))
         where

  private
    H = ⟪ f ⟫ ; J = ⟪ g ⟫
    module H = Hypergraph H
    module J = Hypergraph J
    dihH = dep-irrefl-⟪⟫ f ; dihJ = dep-irrefl-⟪⟫ g
    linH : Linear H
    linH = DAL.⟪⟫-LinearP f
    linJ : Linear J
    linJ = DAL.⟪⟫-LinearP g
    module SF = SS.PerHG H dihH linH
    module SG = SS.PerHG J dihJ linJ
    module RH = Run H
    module RJ = Run J

  open _≅ᴴ_ iso
    using (φ; φ⁻¹; ψ; φ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod; ψ-ein; ψ-eout; atom-ein; atom-eout; ψ-elab)

  φ-inj : Injective _≡_ _≡_ φ
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  di : domL J ≡ domL H
  di = IW.domL-iso iso
  ci : codL J ≡ codL H
  ci = IW.codL-iso iso

  τ : SF.Order
  τ = IW.τ iso

  module TE = DC2.TermEmbedˢ {H} {J}
    φ φ-inj φ-lab ψ ψ-ein ψ-eout atom-ein atom-eout ψ-elab

  mapψτ : map ψ τ ≡ allFin J.nE
  mapψτ = map-∘-id ψ-rght (allFin J.nE)

  mapφdom : map φ H.dom ≡ J.dom
  mapφdom = sym φ-dom

  private
    sH-final : List (Fin H.nV)
    sH-final = proj₁ (RH.process-edgesˢ τ H.dom)

    sJ-final : List (Fin J.nV)
    sJ-final = proj₁ (RJ.process-edgesˢ (allFin J.nE) J.dom)

  fin-eq : sJ-final ≡ map φ sH-final
  fin-eq =
    trans (sym (cong₂ (λ es s → proj₁ (RJ.process-edgesˢ es s)) mapψτ mapφdom))
          (TE.proc-stack-embˢ τ H.dom)

  map-φ-↭⁻ : ∀ {xs ys : List (Fin H.nV)} → map φ xs Perm.↭ map φ ys → xs Perm.↭ ys
  map-φ-↭⁻ {xs} {ys} p with PermProp.↭-map-inv φ p
  ... | ys' , mapφys≡mapφys' , xs↭ys' =
        subst (xs Perm.↭_)
              (sym (map-injective {f = φ} φ-inj mapφys≡mapφys'))
              xs↭ys'

  iso-validˢ : SG.Validˢ (allFin J.nE) → SF.Validˢ τ
  iso-validˢ vJ = map-φ-↭⁻ step
    where
      step : map φ sH-final Perm.↭ map φ H.cod
      step = subst (λ z → z Perm.↭ map φ H.cod) fin-eq (subst (λ z → sJ-final Perm.↭ z) φ-cod vJ)

  open PC.Kit J using (⟦relabel-rigid⟧)

  permute-relabel-freeˢ
    : (vJ : SG.Validˢ (allFin J.nE))
    → RJ.permuteˢ vJ ≈̂ RH.permuteˢ (iso-validˢ vJ)
  permute-relabel-freeˢ vJ =
    ⟦relabel-rigid⟧ H.vlab φ φ-lab (Linear⇒cod-Unique J linJ) fin-eq (sym φ-cod)
                    vJ (iso-validˢ vJ)

  proc-twin
    : ∀ (esJ : List (Fin J.nE)) (sJ : List (Fin J.nV))
    → esJ ≡ map ψ τ → sJ ≡ map φ H.dom
    → proj₂ (RJ.process-edgesˢ esJ sJ) ≈̂ proj₂ (RH.process-edgesˢ τ H.dom)
  proc-twin .(map ψ τ) .(map φ H.dom) refl refl = TE.term-emb-≈̂ τ H.dom

  iso-transportˢ
    : (vJ : SG.Validˢ (allFin J.nE))
    → castˢ di ci (SG.decodeOrdˢ (allFin J.nE) vJ)
      ≈ˢ SF.decodeOrdˢ τ (iso-validˢ vJ)
  iso-transportˢ vJ =
    ≈̂⇒castˢ (∘-resp-≈̂ (permute-relabel-freeˢ vJ)
                      (proc-twin (allFin J.nE) J.dom (sym mapψτ) (sym mapφdom)))
            di ci

  private
    module CPH = PerHG H dihH linH run-interchange-H

  noInvH : SF.NoInv (allFin H.nE)
  noInvH = fin-order-NoInv-⟪⟫ f
  noInvJ : SG.NoInv (allFin J.nE)
  noInvJ = fin-order-NoInv-⟪⟫ g

  NoInv-τ : SF.NoInv τ
  NoInv-τ = IW.NoInv-τ iso noInvJ

  decode-ordˢ-resp-iso
    : (vJ : SG.Validˢ (allFin J.nE))
    → Σ[ vH ∈ SF.Validˢ (allFin H.nE) ]
        castˢ di ci (SG.decodeOrdˢ (allFin J.nE) vJ)
        ≈ˢ SF.decodeOrdˢ (allFin H.nE) vH
  decode-ordˢ-resp-iso vJ =
    let vτ            = iso-validˢ vJ
        transport≈    = iso-transportˢ vJ
        (vH , inv≈)   =
          CPH.order-invariantˢ τ (IW.τ↭allFin iso) NoInv-τ noInvH vτ
    in vH , ≈-trans transport≈ inv≈
