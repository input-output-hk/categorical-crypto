{-# OPTIONS --safe #-}

-- ============================================================================
-- The machine category is symmetric monoidal: the laws relating `_⊗₁_`, `_∘_`,
-- the structural forwarders of `Machine.Core`, and the Kleisli builders `_∘ᴷ_`
-- and `_⊗ᴷ_`, all at `_≅ᴹ_`.  Each is proved in its own module; this one
-- collects them.  The `agda-categories` records themselves are assembled in
-- `CategoricalCrypto.Machine.MonoidalCategory`.
-- ============================================================================

module CategoricalCrypto.Machine.Monoidal where

open import CategoricalCrypto.Machine.Forwarder public
  using (⊗₁-id; ρ-∘ᴷ-fwd; ρ-idᴷ; λ-zip-idᴷ)
open import CategoricalCrypto.Machine.Monoidal.Interchange public
  using (⊗₁-interchange)
open import CategoricalCrypto.Machine.Monoidal.Coherence public
  using (α-isoˡ; α-isoʳ; ρ-isoˡ; ρ-isoʳ; λ-isoˡ; λ-isoʳ; σ-σ; triangle; pentagon; hexagon;
         ∘ᴷ-fwd-decomp; ⊗ᴷ-fwd-decomp; mid4-decomp; absorb-regroup-decomp)
open import CategoricalCrypto.Machine.Monoidal.Associator public
  using (⊗-assoc⃖-natural)
open import CategoricalCrypto.Machine.Monoidal.Unitors public
  using (λ⇒-natural; ρ⇒-natural)
open import CategoricalCrypto.Machine.Monoidal.Braiding public
  using (σ-natural)
open import CategoricalCrypto.Machine.Monoidal.Naturality public
  using (∘ᴷ-fwd-natural; ⊗ᴷ-fwd-natural)
open import CategoricalCrypto.Machine.Monoidal.Kleisli public
  using (∘ᴷ-assoc; ⊗ᴷ-∘ᴷ)
