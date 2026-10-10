{-# OPTIONS --safe --without-K #-}

-- Morphisms between standard setups

module CategoricalCrypto.Standard2.Morphism where

open import Data.Product.Base
open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties.Ext
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.Functor.Properties
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.UCSetup.Morphism

module _ {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
         (𝕄 : MonoidalCategory o ℓ e) (𝕄′ : MonoidalCategory o′ ℓ′ e′)
         (ℰ : Presheaf (MonoidalCategory.U 𝕄) (Setoids cs ℓs))
         (ℰ′ : Presheaf (MonoidalCategory.U 𝕄′) (Setoids cs ℓs))
         (F : StrongMonoidalFunctor 𝕄 𝕄′) where
  private
    module S = StdUC 𝕄 ℰ
    module S′ = StdUC 𝕄′ ℰ′
    module F = StrongMonoidalFunctor F
    module Op = Oplax F
  open MonoidalCategory 𝕄′
  open MonoidalR monoidal
  open MonoidalUtilities.Shorthands monoidal
  open MR U

  StdUCMorphism : PresheafMorphism F.F ℰ ℰ′
                → UCSetupMorphism S.StdSetup S′.StdSetup
  StdUCMorphism ν = record
    { effect = record
      { F = F.F ; Φ = F.monoidalFunctor ; κ = Op.δ
      ; isGradedKleisliMorphism = record
        { κ-return = Op.δ-unitorˡ
        ; κ-sub    = Op.δ-commuteʳ
        ; κ-ext    = ext-law
        }
      }
    ; ν = ν
    }
    where
      ext-law : ∀ {X Y A B} (f : A S.⇒ S.T₀ Y B)
              → Op.δ ∘ F.₁ (S.ext X f)
                ≈ (Op.ψ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (Op.δ ∘ F.₁ f))) ∘ Op.δ
      ext-law f = (refl⟩∘⟨ F.homomorphism) ○ extendʳ Op.δ-assoc′
                ○ (refl⟩∘⟨ Op.δ-commuteˡ f) ○ center (pullʳ merge₂ʳ)

  module _ (ν : PresheafMorphism F.F ℰ ℰ′) where
    open Transfer (StdUCMorphism ν)

    private
      across : ∀ {A B} {u u′ v v′ : A ⇒ B} → u ≈ u′ → v ≈ v′ → u′ S′.≈ℰ v′ → u S′.≈ℰ v
      across p q r = S′.≈ℰ-trans (S′.≈C⇒≈ℰ p) (S′.≈ℰ-trans r (S′.≈ℰ-sym (S′.≈C⇒≈ℰ q)))

      -- At an image ancilla the U-kernel component is `F` of the source's,
      -- conjugated by the oplax structure.
      at-image : ∀ {Y X A B} (h : A S.⇒ X S.⊗₀ B)
            → α⇐ ∘ id {F.₀ Y} ⊗₁ (Op.δ ∘ F.₁ h) ≈ (Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ (S.α⇐ S.∘ S.id S.⊗₁ h) ∘ Op.ψ
      at-image h = ⟺ (begin
        (Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ (S.α⇐ S.∘ S.id S.⊗₁ h) ∘ Op.ψ    ≈⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        (Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ S.α⇐ ∘ F.₁ (S.id S.⊗₁ h) ∘ Op.ψ  ≈⟨ pullˡ (assoc ○ Op.δ-assoc) ⟩
        (α⇐ ∘ id ⊗₁ Op.δ ∘ Op.δ) ∘ F.₁ (S.id S.⊗₁ h) ∘ Op.ψ       ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
        α⇐ ∘ id ⊗₁ Op.δ ∘ Op.δ ∘ F.₁ (S.id S.⊗₁ h) ∘ Op.ψ         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (Op.δ-commuteˡ h) ⟩
        α⇐ ∘ id ⊗₁ Op.δ ∘ (id ⊗₁ F.₁ h ∘ Op.δ) ∘ Op.ψ             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelʳ Op.δψ ⟩
        α⇐ ∘ id ⊗₁ Op.δ ∘ id ⊗₁ F.₁ h                            ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
        α⇐ ∘ id ⊗₁ (Op.δ ∘ F.₁ h)                                ∎)

      -- An ancilla moved along an iso.
      conj : ∀ {Y Y′ P Q R} {u : Y ⇒ Y′} {u⁻ : Y′ ⇒ Y} → u ∘ u⁻ ≈ id → (k : P ⇒ Q ⊗₀ R)
           → α⇐ ∘ id ⊗₁ k ≈ ((u ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ k) ∘ u⁻ ⊗₁ id
      conj {u = u} {u⁻} inv k = ⟺ (begin
        ((u ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ k) ∘ u⁻ ⊗₁ id
          ≈⟨ refl⟩∘⟨ pullʳ (merge₁ʳ ○ (identityˡ ⟩⊗⟨refl) ○ serialize₁₂) ⟩
        ((u ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ u⁻ ⊗₁ id ∘ id ⊗₁ k
          ≈⟨ refl⟩∘⟨ pullˡ ((refl⟩∘⟨ (refl⟩⊗⟨ ⟺ ⊗.identity)) ○ assoc-commute-to) ⟩
        ((u ⊗₁ id) ⊗₁ id) ∘ ((u⁻ ⊗₁ id) ⊗₁ id ∘ α⇐) ∘ id ⊗₁ k
          ≈⟨ refl⟩∘⟨ assoc ⟩
        ((u ⊗₁ id) ⊗₁ id) ∘ (u⁻ ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ k
          ≈⟨ cancelˡ (merge₁ˡ ○ ((merge₁ˡ ○ (inv ⟩⊗⟨refl) ○ ⊗.identity) ⟩⊗⟨refl) ○ ⊗.identity) ⟩
        α⇐ ∘ id ⊗₁ k ∎)

    -- Every target ancilla is an image up to iso, so `≈ℰ` crossing suffices
    -- without the target's `GradeStable`.
    surjective⇒preserves-≈ᵁ : EssentiallySurjective F.F → Preserves-≈ℰ → Preserves-≈ᵁ
    surjective⇒preserves-≈ᵁ surj pres {f = f} {g} e Y′ =
      let Y , i = surj Y′ in
      across (conj (Mor._≅_.isoʳ i) _) (conj (Mor._≅_.isoʳ i) _)
        (S′.≈ℰ-cong-post _ (S′.≈ℰ-cong-pre _
          (across (at-image f) (at-image g) (S′.≈ℰ-cong-post _ (S′.≈ℰ-cong-pre _ (pres (e Y)))))))
