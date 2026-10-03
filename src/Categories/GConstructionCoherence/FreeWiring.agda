{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Verbatim free twins of `GConstructionTrace`'s routing isos `β`, `α`, `γ`,
-- `mid`, over any solver signature: the transported coherence lemmas are read
-- off by conversion against the originals.
--------------------------------------------------------------------------------

open import Categories.APROP using (APROPSignature; module APROP)

module Categories.GConstructionCoherence.FreeWiring (sig : APROPSignature) where

open APROP sig

βᵗ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
βᵗ = α⇐ ∘ id ⊗₁ σ ∘ α⇒

αᵗ : ∀ {A⁻ B⁺ B⁻ C⁺} → HomTerm ((B⁻ ⊗₀ C⁺) ⊗₀ (A⁻ ⊗₀ B⁺)) ((A⁻ ⊗₀ C⁺) ⊗₀ (B⁻ ⊗₀ B⁺))
αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γᵗ : ∀ {A⁺ B⁺ B⁻ C⁻} → HomTerm ((A⁺ ⊗₀ C⁻) ⊗₀ (B⁻ ⊗₀ B⁺)) ((B⁺ ⊗₀ C⁻) ⊗₀ (A⁺ ⊗₀ B⁻))
γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒
