{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- `σ-block-⊗`: braiding a TENSOR block `(A₁ ⊗ A₂)` past `B` decomposes
-- into braiding `A₂` past `B` then `A₁` past `B`.  The inductive engine
-- of the block bridge.  Derived from `hexagon₂` (now available at the
-- `d`-level) + associator coherence.
--
--   σ-block {A₁ ⊗ A₂} {B} {C}
--     ≈ (id ⊗ α⇐) ∘ σ-block {A₁} {B} {A₂ ⊗ C}
--             ∘ (id ⊗ σ-block {A₂} {B} {C}) ∘ α⇒
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.SigmaBlockTensor
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon d
  using (σ-block; hexagon₂)

open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- `σ-block` solved out of `hexagon₂`: express the tensor-σ in terms of
-- the component σ's.

σ⊗-from-hexagon₂
  : ∀ {A₁ A₂ B : ObjTerm}
  → σ {A = A₁ ⊗₀ A₂} {B = B}
    ≈Term
    α⇒ {A = B} {B = A₁} {C = A₂}
      ∘ ((σ {A = A₁} {B = B} ⊗₁ id {A = A₂})
          ∘ α⇐ {A = A₁} {B = B} {C = A₂}
          ∘ (id {A = A₁} ⊗₁ σ {A = A₂} {B = B}))
      ∘ α⇒ {A = A₁} {B = A₂} {C = B}
σ⊗-from-hexagon₂ {A₁} {A₂} {B} = begin
    σ {A = A₁ ⊗₀ A₂} {B = B}
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ σ
      ≈⟨ ∘-resp-≈ (≈-Term-sym α⇒∘α⇐≈id) ≈-Term-refl ⟩
    (α⇒ ∘ α⇐) ∘ σ
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
    (α⇒ ∘ α⇐) ∘ (σ ∘ id)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇐∘α⇒≈id)) ⟩
    (α⇒ ∘ α⇐) ∘ (σ ∘ (α⇐ ∘ α⇒))
      ≈⟨ assoc ⟩
    α⇒ ∘ (α⇐ ∘ (σ ∘ (α⇐ ∘ α⇒)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    α⇒ ∘ (α⇐ ∘ ((σ ∘ α⇐) ∘ α⇒))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    α⇒ ∘ ((α⇐ ∘ (σ ∘ α⇐)) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym hexagon₂) ≈-Term-refl) ⟩
    α⇒ {A = B} {B = A₁} {C = A₂}
      ∘ (((σ {A = A₁} {B = B} ⊗₁ id {A = A₂})
            ∘ α⇐ {A = A₁} {B = B} {C = A₂}
            ∘ (id {A = A₁} ⊗₁ σ {A = A₂} {B = B}))
          ∘ α⇒ {A = A₁} {B = A₂} {C = B})
  ∎
