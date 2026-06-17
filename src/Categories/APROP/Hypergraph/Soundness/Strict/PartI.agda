{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Part (I)ˢ of the strictified soundness proof: the strict roundtrip
--
--     st-≈-decodePˢ : ∀ f → st f ≈ˢ decodePˢ f
--
-- by induction on `f`, combining the per-constructor decoder shape lemmas.
-- The atomic (id/λ/ρ/α), σ, ∘, and `Agen` (single-generator base case)
-- shapes are wired CONCRETELY (their deferred `permˢ-K`/`bswap-σ` are
-- discharged axiom-free by `Strict.PermK` and `Strict.BlockSwapComm`, and
-- `Agen` is concrete via `Strict.Decode.DecodeGen`).  ONE shape — ⊗ (via the
-- K-prepend box-braid `KBlockσ`) — is taken as a module parameter, so this
-- assembly is unconditional given exactly that one.
--
-- Composed with `Boundary.st-roundtrip` (embF (st f) ≈Term bridge f) and
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

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)

open import Categories.FreeMonoidal using (v≤v)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (st)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes   sig _≟X_ as DSh
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma   sig _≟X_ as DSig
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeComposeAssembly sig _≟X_ as DComp
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK          sig _≟X_ as PK
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm  sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeGen      sig _≟X_ as DGen

--------------------------------------------------------------------------------
-- The concretely-discharged shapes (atomic + σ + ∘).

private
  -- σ shape (DecodeSigma, at concrete permˢ-K + bswap-σ)
  d-σ : ∀ A B → decodePˢ (σ {A} {B}) ≈ˢ σˢ (flatten A) (flatten B)
  d-σ A B = DSig.Sigma.decodePˢ-σ PK.permˢ-K BSC.block-swap-comm A B

  -- ∘ shape (DecodeComposeAssembly, unconditional)
  d-∘ : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
      → decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
  d-∘ g f = DComp.ComposeShape.decodePˢ-∘-shape g f

--------------------------------------------------------------------------------
-- The induction, parameterised over the single remaining shape (decodePˢ-⊗);
-- `Agen` is now concrete via DecodeGen.

module _
  (decodePˢ-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g)
  where

  -- the Agen base case is now CONCRETE (DecodeGen, fully proven)
  decodePˢ-Agen : ∀ {A B} (g : mor A B) → decodePˢ (Agen g) ≈ˢ st (Agen g)
  decodePˢ-Agen = DGen.decodePˢ-Agen

  st-≈-decodePˢ : ∀ {A B} (f : HomTerm A B) → st f ≈ˢ decodePˢ f
  st-≈-decodePˢ (Agen g)        = ≈-sym (decodePˢ-Agen g)
  st-≈-decodePˢ (id {A})        = ≈-sym (DSh.decodePˢ-id PK.permˢ-K {A})
  st-≈-decodePˢ (g ∘ f)         =
    ≈-trans (∘-resp (st-≈-decodePˢ g) (st-≈-decodePˢ f))
            (≈-sym (d-∘ g f))
  st-≈-decodePˢ (f ⊗₁ g)        =
    ≈-trans (⊗-resp (st-≈-decodePˢ f) (st-≈-decodePˢ g))
            (≈-sym (decodePˢ-⊗ f g))
  st-≈-decodePˢ (λ⇒ {A})        = ≈-sym (DSh.decodePˢ-λ⇒ PK.permˢ-K {A})
  st-≈-decodePˢ (λ⇐ {A})        = ≈-sym (DSh.decodePˢ-λ⇐ PK.permˢ-K {A})
  st-≈-decodePˢ (ρ⇒ {A})        = ≈-sym (DSh.decodePˢ-ρ⇒ PK.permˢ-K {A})
  st-≈-decodePˢ (ρ⇐ {A})        = ≈-sym (DSh.decodePˢ-ρ⇐ PK.permˢ-K {A})
  st-≈-decodePˢ (α⇒ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇒ PK.permˢ-K {A} {B} {C})
  st-≈-decodePˢ (α⇐ {A} {B} {C}) = ≈-sym (DSh.decodePˢ-α⇐ PK.permˢ-K {A} {B} {C})
  st-≈-decodePˢ (σ {A} {B} ⦃ v≤v ⦄) = ≈-sym (d-σ A B)
