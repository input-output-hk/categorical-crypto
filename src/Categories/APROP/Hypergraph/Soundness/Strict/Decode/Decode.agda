{-# OPTIONS --safe --without-K #-}

-- The strict run uses the non-strict `process-edges` stack definitionally;
-- its totality witness therefore transfers without a stack cast.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen)
open FreeMonoidalHelper Symm X using (flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig public

open import Data.Fin using (Fin)

module Run (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open StrictDecoder H public

  runˢ : Σ[ s ∈ List (Fin H.nV) ] HomS (map vl H.dom) (map vl s)
  runˢ = process-edgesˢ (allFin H.nE) H.dom

  s-finˢ : List (Fin H.nV)
  s-finˢ = proj₁ runˢ

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫

  finalPermˢ : RF.s-finˢ Perm.↭ Hf.cod
  finalPermˢ = decode-attempt-LinearP f

decodePˢ : ∀ {A B} (f : HomTerm A B) → HomS (flatten A) (flatten B)
decodePˢ f =
  castˢ (⟪⟫-domL f) (⟪⟫-codL f)
    (Run.permuteˢ ⟪ f ⟫ (finalPermˢ f) ∘ˢ proj₂ (Run.runˢ ⟪ f ⟫))
