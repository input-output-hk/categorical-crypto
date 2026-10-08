{-# OPTIONS --safe --without-K #-}

-- The σ decoder shape uses the definitionally chosen `bswap`.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (module hGenSwap-impl)
open FreeMonoidalHelper Symm X using (flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
  using (bswap)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig
  as BSC

open import Data.Fin using (Fin)
open Perm using (_↭_)

module Sigma (A B : ObjTerm) where
  private
    f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
    f = σ {A} {B}

    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫
    open Restrict (Fin Hf.nV) Hf.vlab

    open hGenSwap-impl A B using (Lblk; Rblk; lem-L; lem-R)

    bsw : Hf.dom ↭ Hf.cod
    bsw = bswap Lblk Rblk

  σ-block-≈ : RF.permuteˢ bsw ≈ᵛ σᵛ Lblk Rblk
  σ-block-≈ = BSC.block-swap-comm (Fin Hf.nV) Hf.vlab Lblk Rblk

  inner≈ : RF.permuteˢ (finalPermˢ f) ∘ᵛ proj₂ RF.runˢ ≈ᵛ σᵛ Lblk Rblk
  inner≈ = ≈-trans idʳ σ-block-≈

  decodePˢ-σ : decodePˢ f ≈ˢ σˢ (flatten A) (flatten B)
  decodePˢ-σ =
    ≈̂⇒castˢ
      (≈̂-trans (≈ˢ⇒≈̂ inner≈)
               (≈̂-trans (σᵛ-≈̂ Lblk Rblk) (σ-≈̂ lem-L lem-R)))
      (⟪⟫-domL f) (⟪⟫-codL f)

