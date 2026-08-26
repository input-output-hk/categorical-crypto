{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Part (I)ˢ of the strictified soundness proof: the strict roundtrip
--
--     st-≈-decodePˢ : ∀ f → st f ≈ˢ decodePˢ f
--
-- by induction on `f`, combining the per-constructor decoder shape lemmas.
-- The atomic (id/λ/ρ/α), σ, ∘, and `Agen` (single-generator base case)
-- shapes are wired CONCRETELY (the σ-shape's `bswap-σ` is discharged by
-- `Strict.Interchange.BlockSwapComm`, `Agen` by `Strict.Decode.DecodeGen`).
-- ONE shape — ⊗ (via the K-prepend box-braid `KBlockσ`) — is taken as a
-- module parameter, so this assembly is unconditional given exactly that
-- one.
--
-- Composed with `Strict.Soundness.st-roundtrip` (embF (st f) ≈Term bridge f) and
-- part (II)ˢ (`decodePˢ`-iso-invariance), this yields the re-pointed
-- soundness theorem.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.PartI
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.FreeMonoidal using (v≤v)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_ using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes   sig _≟X_ as DSh
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma   sig _≟X_ as DSig
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeComposeAssembly sig _≟X_ as DComp
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm  sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeGen      sig _≟X_ as DGen

--------------------------------------------------------------------------------
-- The induction, parameterised over the single remaining shape (decodePˢ-⊗).
-- Every other clause names the discharging lemma directly: re-ascribing its
-- statement here would only restate it.

module _
  (decodePˢ-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g)
  where

  st-≈-decodePˢ : ∀ {A B} (f : HomTerm A B) → st f ≈ˢ decodePˢ f
  st-≈-decodePˢ (Agen g)        = ≈-sym (DGen.decodePˢ-Agen g)
  st-≈-decodePˢ (id {A})        = ≈-sym (DSh.decodePˢ-id {A})
  st-≈-decodePˢ (g ∘ f)         =
    ≈-trans (∘-resp (st-≈-decodePˢ g) (st-≈-decodePˢ f))
            (≈-sym (DComp.ComposeShape.decodePˢ-∘-shape g f))
  st-≈-decodePˢ (f ⊗₁ g)        =
    ≈-trans (⊗-resp (st-≈-decodePˢ f) (st-≈-decodePˢ g))
            (≈-sym (decodePˢ-⊗ f g))
  st-≈-decodePˢ (λ⇒ {A})        = ≈-sym (DSh.decodePˢ-λ⇒ {A})
  st-≈-decodePˢ (λ⇐ {A})        = ≈-sym (DSh.decodePˢ-λ⇐ {A})
  st-≈-decodePˢ (ρ⇒ {A})        = ≈-sym (DSh.decodePˢ-ρ⇒ {A})
  st-≈-decodePˢ (ρ⇐ {A})        = ≈-sym (DSh.decodePˢ-ρ⇐ {A})
  st-≈-decodePˢ (α⇒ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇒ {A} {B} {C})
  st-≈-decodePˢ (α⇐ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇐ {A} {B} {C})
  st-≈-decodePˢ (σ {A} {B} ⦃ v≤v ⦄) =
    ≈-sym (DSig.Sigma.decodePˢ-σ BSC.block-swap-comm A B)
