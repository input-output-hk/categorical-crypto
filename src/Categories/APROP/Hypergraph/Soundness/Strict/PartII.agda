{-# OPTIONS --safe --without-K #-}

-- Decoder invariance under hypergraph isomorphism.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.PartII
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig using (dep-irrefl-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig using (Linear⇒cod-Unique)
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
  using (decodePˢ; finalPermˢ)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.FireMid sig as FMD
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig
  using (run-interchange-tailˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig as SS
import Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoTransport sig as IT

open import Data.List.Properties

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    F   = ⟪ f ⟫
    dih = dep-irrefl-⟪⟫ f
    lin : Linear F
    lin = DAL.⟪⟫-LinearP f

  open SS.PerHG F dih lin using (Validˢ)

  vrangeˢ : Validˢ (allFin (Hypergraph.nE F))
  vrangeˢ = finalPermˢ f

  run-interchange-H : SS.PerHG.RunInterchangeAt F dih lin
  run-interchange-H ps qs {e} {e'} inc res-full =
    run-interchange-tailˢ F ps qs inc res-full
      (record { reshuffle = proj₁ ri₀ ; run-eq = proj₂ ri₀ })
    where
      res-empty-tail : SUR.Reservoir≤1 F (ps ++ e' ∷ e ∷ []) (Hypergraph.dom F)
      res-empty-tail =
        SUR.reservoir-prefix F (ps ++ e' ∷ e ∷ []) qs (Hypergraph.dom F)
          (subst (λ z → SUR.Reservoir≤1 F z (Hypergraph.dom F))
                 (sym (++-assoc ps (e' ∷ e ∷ []) qs)) res-full)

      ri₀ = FMD.run-interchange₀ˢ F lin ps inc res-empty-tail

module Boundary {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫) where
  private
    F = ⟪ f ⟫ ; G = ⟪ g ⟫
    dihF = dep-irrefl-⟪⟫ f ; dihG = dep-irrefl-⟪⟫ g
    linF : Linear F
    linF = DAL.⟪⟫-LinearP f
    linG : Linear G
    linG = DAL.⟪⟫-LinearP g
    module SF = SS.PerHG F dihF linF
    module SG = SS.PerHG G dihG linG

    perm-rigidˢ-F = StrictDecoder.rigidˢ F

    rng-F = allFin (Hypergraph.nE F)
    rng-G = allFin (Hypergraph.nE G)

    df = ⟪⟫-domL f ; cf = ⟪⟫-codL f
    dg = ⟪⟫-domL g ; cg = ⟪⟫-codL g
    di = IW.domL-iso iso ; ci = IW.codL-iso iso

  decodeOrdˢ-witness-coh
    : ∀ (v w : SF.Validˢ rng-F)
    → SF.decodeOrdˢ rng-F v ≈ˢ SF.decodeOrdˢ rng-F w
  decodeOrdˢ-witness-coh v w = ∘-resp (perm-rigidˢ-F (Linear⇒cod-Unique F linF) v w) ≈-refl

  decodeOrdˢ-boundary-resp-≈
    : ∀ (vf : SF.Validˢ rng-F) (vg : SG.Validˢ rng-G) (vH : SF.Validˢ rng-F)
    → castˢ di ci (SG.decodeOrdˢ rng-G vg) ≈ˢ SF.decodeOrdˢ rng-F vH
    → castˢ df cf (SF.decodeOrdˢ rng-F vf)
      ≈ˢ castˢ dg cg (SG.decodeOrdˢ rng-G vg)
  decodeOrdˢ-boundary-resp-≈ vf vg vH wiring≈ =
    viâ cast-≈̂
        (≈̂-trans (≈ˢ⇒≈̂ (decodeOrdˢ-witness-coh vf vH))
                 (≈̂-sym (castˢ⇒≈̂ di ci wiring≈)))
        cast-≈̂

decodePˢ-resp-iso : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decodePˢ f ≈ˢ decodePˢ g
decodePˢ-resp-iso f g iso =
  B.decodeOrdˢ-boundary-resp-≈ (vrangeˢ f) (vrangeˢ g) (proj₁ res) (proj₂ res)
  where
    module B = Boundary f g iso
    res = IT.decode-ordˢ-resp-iso f g iso (run-interchange-H f) (vrangeˢ g)
