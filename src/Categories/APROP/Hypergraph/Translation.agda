{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation ⟪_⟫ : HomTerm → Hypergraph using the PRUNED `hComposeP`.
--
-- Same as `FromAPROP.⟪_⟫` except `∘` uses `hComposeP` (Option A) rather
-- than `hCompose`. This version enables the group-(b)/(c) ≈Term axioms
-- (idˡ, idʳ, etc.) where the LHS would otherwise have strictly more
-- vertices than the RHS due to unreachable K-side dom vertices.
--
-- Separate file because `FromAPROP` can't import `PrunedCompose` — the
-- latter imports `FromAPROP` for `FlatGen`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Translation (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hGen; hId; hTensor; hSwap)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)

open import Data.List using (_++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (refl; subst₂)

--------------------------------------------------------------------------------
-- Translation from APROP terms.
--
-- Structurally identical to the original `FromAPROP.⟪_⟫`, except `∘`
-- dispatches to `hComposeP` for the canonical pruned cospan composition.

⟪_⟫ : ∀ {A B} → HomTerm A B → Hypergraph FlatGen (flatten A) (flatten B)

⟪ Agen f ⟫ = hGen f
⟪ id {A} ⟫ = hId A
⟪ g ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ g ⟫
⟪ f ⊗₁ g ⟫ = hTensor ⟪ f ⟫ ⟪ g ⟫

-- Unitors: flatten(unit ⊗ A) = flatten A definitionally, so λ⇒ is hId A.
⟪ λ⇒ {A} ⟫ = hId A
⟪ λ⇐ {A} ⟫ = hId A

-- ρ⇒/ρ⇐ need `flatten A ++ [] ≡ flatten A` (`++-identityʳ`).
⟪ ρ⇒ {A} ⟫ = subst₂ (Hypergraph FlatGen)
              refl (++-identityʳ (flatten A)) (hId (A ⊗₀ unit))
⟪ ρ⇐ {A} ⟫ = subst₂ (Hypergraph FlatGen)
              (++-identityʳ (flatten A)) refl (hId (A ⊗₀ unit))

-- Associators: need `(xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)`.
⟪ α⇒ {A} {B} {C} ⟫ = subst₂ (Hypergraph FlatGen)
                       refl (++-assoc (flatten A) (flatten B) (flatten C))
                       (hId ((A ⊗₀ B) ⊗₀ C))
⟪ α⇐ {A} {B} {C} ⟫ = subst₂ (Hypergraph FlatGen)
                       (++-assoc (flatten A) (flatten B) (flatten C)) refl
                       (hId ((A ⊗₀ B) ⊗₀ C))

-- Braiding.
⟪ σ {A} {B} ⟫ = hSwap A B
