{-# OPTIONS --safe --without-K #-}

-- Strict roundtrip by induction on the term, using decoder shape lemmas.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.PartI
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeComposeAssembly sig as DComp
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeGen sig as DGen
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig as DSh
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig as DSig
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig as TB

st-≈-decodePˢ : ∀ {A B} (f : HomTerm A B) → st f ≈ˢ decodePˢ f
st-≈-decodePˢ (Agen g)        = ≈-sym (DGen.Gen.decodePˢ-Agen g)
st-≈-decodePˢ (id {A})        = ≈-sym (DSh.decodePˢ-id {A})
st-≈-decodePˢ (g ∘ f)         =
  ≈-trans (∘-resp (st-≈-decodePˢ g) (st-≈-decodePˢ f))
          (≈-sym (DComp.ComposeShape.decodePˢ-∘-shape g f))
st-≈-decodePˢ (f ⊗₁ g)        =
  ≈-trans (⊗-resp (st-≈-decodePˢ f) (st-≈-decodePˢ g))
          (≈-sym (TB.decodePˢ-⊗-concrete f g))
st-≈-decodePˢ (λ⇒ {A})        = ≈-sym (DSh.decodePˢ-λ⇒ {A})
st-≈-decodePˢ (λ⇐ {A})        = ≈-sym (DSh.decodePˢ-λ⇐ {A})
st-≈-decodePˢ (ρ⇒ {A})        = ≈-sym (DSh.decodePˢ-ρ⇒ {A})
st-≈-decodePˢ (ρ⇐ {A})        = ≈-sym (DSh.decodePˢ-ρ⇐ {A})
st-≈-decodePˢ (α⇒ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇒ {A} {B} {C})
st-≈-decodePˢ (α⇐ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇐ {A} {B} {C})
st-≈-decodePˢ (σ {A} {B} ⦃ v≤v ⦄) =
  ≈-sym (DSig.Sigma.decodePˢ-σ A B)
