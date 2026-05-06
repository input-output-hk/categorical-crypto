{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Triangle equation: (id ⊗ λ⇒) ∘ α⇒ ≈ ρ⇒ ⊗ id.
--
-- Constructive proof under de-indexing.  Strategy:
--
--   * LHS = ⟪(id ⊗ λ⇒) ∘ α⇒⟫
--         = hComposeP (hId ((A ⊗ unit) ⊗ B)) (hId (A ⊗ B)) bdy
--           [since ⟪α⇒⟫ = hId ((A ⊗ unit) ⊗ B) and
--                 ⟪id ⊗ λ⇒⟫ = hTensor (hId A) (hId B) = hId (A ⊗ B)]
--   * Apply `hCompose-hId-L-iso-flex` to get ≅ᴴ hId (A ⊗ B).
--   * RHS = ⟪ρ⇒ ⊗ id⟫ = hTensor (hId (A ⊗ unit)) (hId B)
--                     = hTensor (hTensor (hId A) hEmpty) (hId B)
--   * Use `hTensor-resp-≅ᴴ (sym hTensor-G-hEmpty-iso) refl` to
--     bridge `hId (A ⊗ B) = hTensor (hId A) (hId B)` and the RHS.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Triangle (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty; domL-hId)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)
open import Categories.APROP.Hypergraph.Invariant sig using (hId-dom-Unique)
open import Categories.APROP.Hypergraph.Congruence sig using (hTensor-resp-≅ᴴ)
open import Categories.APROP.Hypergraph.SoundnessProved sig
  using (hCompose-hId-L-iso-flex; hTensor-G-hEmpty-iso)

open import Data.List using (_++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong)

triangle-sound
  : ∀ {A B}
  → ⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A} {unit} {B} ⟫
  ≅ᴴ ⟪ ρ⇒ {A} ⊗₁ id {B} ⟫
triangle-sound {A}{B} =
  trans-≅ᴴ
    (hCompose-hId-L-iso-flex ((A ⊗₀ unit) ⊗₀ B) (hId (A ⊗₀ B))
       K-domL≡flat
       (trans (⟪⟫-codL (α⇒ {A}{unit}{B}))
              (sym (⟪⟫-domL (id {A} ⊗₁ λ⇒ {B}))))
       (hId-dom-Unique (A ⊗₀ B)))
    (hTensor-resp-≅ᴴ
       (sym-≅ᴴ (hTensor-G-hEmpty-iso (hId A)))
       (refl-≅ᴴ (hId B)))
  where
    K-domL≡flat : domL (hId (A ⊗₀ B)) ≡ flatten ((A ⊗₀ unit) ⊗₀ B)
    K-domL≡flat =
      trans (domL-hId (A ⊗₀ B))
            (sym (cong (_++ flatten B) (++-identityʳ (flatten A))))
