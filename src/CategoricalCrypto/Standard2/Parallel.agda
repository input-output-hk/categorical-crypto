{-# OPTIONS --safe --without-K #-}

-- In the standard model, ≈ᵁ already tests every left tensor context.
-- Symmetry turns right tensor contexts into left ones, so parallel
-- composition needs no preservation assumption on the observation presheaf.

module CategoricalCrypto.Standard2.Parallel where

open import Data.Product
open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Interchange.Braided as Interchange
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
open import Categories.Category.Monoidal.Symmetric
import Categories.Functor.Monoidal.CurriedTensor.Properties as TensorProperties
open import Categories.Functor.Presheaf
import Categories.Morphism.Reasoning as MorphismReasoning

open import CategoricalCrypto.Abstract2.Parallel
open import CategoricalCrypto.Standard2

module Parallel
  {o ℓ e cs ℓs : Level}
  (machines : MonoidalCategory o ℓ e)
  (ℰ-standard : Presheaf (MonoidalCategory.U machines) (Setoids cs ℓs))
  (symmetric : Symmetric (MonoidalCategory.monoidal machines))
  where

  open StdUC machines ℰ-standard
  open BraidedProperties.Shorthands (Symmetric.braided symmetric)
  open Interchange (Symmetric.braided symmetric)
  open MonoidalReasoning monoidal
  open MorphismReasoning ∣machines∣
  open TensorProperties machines
  private
    module Br = Braided (Symmetric.braided symmetric)
    module Generic = ParallelUC StdSetup monoidal

  private variable
    A B C D W X X′ Y Y′ : Channel
    f f′ : A ⇒ X ⊗₀ B
    h h′ : C ⇒ Y ⊗₀ D

  parallelEffect : Generic.ParallelEffect
  parallelEffect = record
    { χ = swapInner.from
    ; χ-sub = λ a b →
        (refl⟩∘⟨ (sub-⊗ a ⟩⊗⟨ sub-⊗ b)) ○ swapInner-natural ○
        (((refl⟩⊗⟨ ⊗.identity) ○ ⟺ (sub-⊗ (a ⊗₁ b))) ⟩∘⟨refl)
    }

  open Generic.ParallelEffect parallelEffect public using (_⊠_; ⊠-sub; ParallelStable)

  ≈ᵁ⇒⊗ˡ : f ≈ᵁ f′ → (W : Channel) → id {W} ⊗₁ f ≈ℰ id ⊗₁ f′
  ≈ᵁ⇒⊗ˡ {f = f} {f′} eq W =
    ≈ℰ-trans (≈C⇒≈ℰ (⟺ (undo f)))
      (≈ℰ-trans (≈ℰ-cong-post α⇒ (eq W)) (≈C⇒≈ℰ (undo f′)))
    where
    undo : (k : A ⇒ X ⊗₀ B) → α⇒ ∘ prefix W k ≈ id ⊗₁ k
    undo k = cancelˡ associator.isoʳ

  ⊗ˡ⇒≈ᵁ : ((W : Channel) → id {W} ⊗₁ f ≈ℰ id ⊗₁ f′) → f ≈ᵁ f′
  ⊗ˡ⇒≈ᵁ eq W = ≈ℰ-cong-post α⇐ (eq W)

  ≈ᵁ-cong-post : (k : X ⊗₀ B ⇒ Y ⊗₀ D) → f ≈ᵁ f′ → k ∘ f ≈ᵁ k ∘ f′
  ≈ᵁ-cong-post k eq = ⊗ˡ⇒≈ᵁ λ W →
    ≈ℰ-trans (≈C⇒≈ℰ split₂ˡ)
      (≈ℰ-trans (≈ℰ-cong-post (id ⊗₁ k) (≈ᵁ⇒⊗ˡ eq W)) (≈C⇒≈ℰ (⟺ split₂ˡ)))

  ≈ᵁ-cong-pre : (k : C ⇒ A) → f ≈ᵁ f′ → f ∘ k ≈ᵁ f′ ∘ k
  ≈ᵁ-cong-pre k eq = ⊗ˡ⇒≈ᵁ λ W →
    ≈ℰ-trans (≈C⇒≈ℰ split₂ˡ)
      (≈ℰ-trans (≈ℰ-cong-pre (id ⊗₁ k) (≈ᵁ⇒⊗ˡ eq W)) (≈C⇒≈ℰ (⟺ split₂ˡ)))

  ⊗ˡ-cong-≈ᵁ : (W : Channel) → f ≈ᵁ f′ → id {W} ⊗₁ f ≈ᵁ id ⊗₁ f′
  ⊗ˡ-cong-≈ᵁ {f = f} {f′} W eq = ⊗ˡ⇒≈ᵁ λ P →
    ≈ℰ-trans (≈C⇒≈ℰ (reassociate P f))
      (≈ℰ-trans (≈ℰ-cong-pre α⇐ (≈ℰ-cong-post α⇒ (≈ᵁ⇒⊗ˡ eq (P ⊗₀ W))))
        (≈C⇒≈ℰ (⟺ (reassociate P f′))))
    where
    reassociate : (P : Channel) (k : A ⇒ X ⊗₀ B)
                → id {P} ⊗₁ (id {W} ⊗₁ k) ≈ (α⇒ ∘ id {P ⊗₀ W} ⊗₁ k) ∘ α⇐
    reassociate P k = switch-fromtoʳ associator
      (⟺ assoc-commute-from ○ (refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl)))

  ⊗ʳ-cong-≈ᵁ : (W : Channel) → f ≈ᵁ f′ → f ⊗₁ id {W} ≈ᵁ f′ ⊗₁ id
  ⊗ʳ-cong-≈ᵁ {f = f} {f′} W eq =
    ≈ᵁ-trans (≈C⇒≈ᵁ (exchange f))
      (≈ᵁ-trans (≈ᵁ-cong-post σ⇐ (≈ᵁ-cong-pre σ⇒ (⊗ˡ-cong-≈ᵁ W eq)))
        (≈ᵁ-sym (≈C⇒≈ᵁ (exchange f′))))
    where
    exchange : (k : A ⇒ X ⊗₀ B) → k ⊗₁ id {W} ≈ σ⇐ ∘ (id ⊗₁ k) ∘ σ⇒
    exchange k = switch-fromtoˡ σ (Br.braiding.⇒.commute (k , id))

  ⊗-cong-≈ᵁ : f ≈ᵁ f′ → h ≈ᵁ h′ → f ⊗₁ h ≈ᵁ f′ ⊗₁ h′
  ⊗-cong-≈ᵁ {f′ = f′} {h = h} ef eh =
    ≈ᵁ-trans (≈C⇒≈ᵁ serialize₂₁)
      (≈ᵁ-trans (≈ᵁ-cong-post (id ⊗₁ h) (⊗ʳ-cong-≈ᵁ _ ef))
        (≈ᵁ-trans (≈ᵁ-cong-pre (f′ ⊗₁ id) (⊗ˡ-cong-≈ᵁ _ eh))
          (≈ᵁ-sym (≈C⇒≈ᵁ serialize₂₁))))

  ⊠-cong-≈ᵁ : ParallelStable
  ⊠-cong-≈ᵁ ef eh = ≈ᵁ-cong-post swapInner.from (⊗-cong-≈ᵁ ef eh)

  UC-⊠ : {f : A ⇒ X ⊗₀ B} {g : A ⇒ X′ ⊗₀ B}
         {h : C ⇒ Y ⊗₀ D} {k : C ⇒ Y′ ⊗₀ D}
       → f ≤UC g → h ≤UC k → f ⊠ h ≤UC g ⊠ k
  UC-⊠ = Generic.ParallelEffect.UC-⊠ parallelEffect ⊠-cong-≈ᵁ
