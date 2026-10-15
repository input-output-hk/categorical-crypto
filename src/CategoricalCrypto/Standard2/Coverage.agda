{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Standard2.Coverage where

open import Data.Product.Base
open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Category.Monoidal.Utilities as Utilities
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties.Ext
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.Functor.Properties
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UCSetup.Coverage
open import CategoricalCrypto.UCSetup.Morphism

module Coverage {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
                (𝕄 : MonoidalCategory o ℓ e) (𝕄′ : MonoidalCategory o′ ℓ′ e′)
                (ℰ : Presheaf (MonoidalCategory.U 𝕄) (Setoids cs ℓs))
                (ℰ′ : Presheaf (MonoidalCategory.U 𝕄′) (Setoids cs ℓs))
                (F : StrongMonoidalFunctor 𝕄 𝕄′)
                (ν : PresheafMorphism (StrongMonoidalFunctor.F F) ℰ ℰ′) where
  private
    module S = StdUC 𝕄 ℰ
    module T = StdUC 𝕄′ ℰ′
    module F = StrongMonoidalFunctor F
    module Op = Oplax F
  open MonoidalCategory 𝕄′
  open MonoidalR monoidal
  open Utilities.Shorthands monoidal
  open MR U
  open Transfer (StdUCMorphism 𝕄 𝕄′ ℰ ℰ′ F ν)
  private
    at-image′ : ∀ {Y X A B} (h : A S.⇒ X S.⊗₀ B)
      → T.prefix (F.₀ Y) (G h) ≈ (Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ (S.prefix Y h) ∘ Op.ψ
    at-image′ = at-image 𝕄 𝕄′ ℰ ℰ′ F ν

    across′ : ∀ {A B} {u u′ v v′ : A ⇒ B} → u ≈ u′ → v ≈ v′ → u′ T.≈ℰ v′ → u T.≈ℰ v
    across′ = across 𝕄 𝕄′ ℰ ℰ′ F ν

    conj′ : ∀ {Y Y′ P Q R} {u : Y ⇒ Y′} {u⁻ : Y′ ⇒ Y} → u ∘ u⁻ ≈ id → (k : P ⇒ Q ⊗₀ R)
      → T.prefix Y′ k ≈ ((u ⊗₁ id) ⊗₁ id) ∘ T.prefix Y k ∘ u⁻ ⊗₁ id
    conj′ = conj 𝕄 𝕄′ ℰ ℰ′ F ν

  record ContextRepresentation (W : T.Channel) : Set (o ⊔ e′ ⊔ ℓ′) where
    field source : S.Channel
          iso : Mor._≅_ U (F.₀ source) W

  record AncillaCoverage : Set (o ⊔ o′ ⊔ e′ ⊔ ℓ′) where
    field represent : (W : T.Channel) → ContextRepresentation W

  essentiallySurjective⇒AncillaCoverage : EssentiallySurjective F.F → AncillaCoverage
  essentiallySurjective⇒AncillaCoverage surj = record { represent = λ W →
    let V , i = surj W in record { source = V ; iso = i } }

  image-component : Preserves-≈ℰ → ∀ {A B X} {f g : A S.⇒ S.T₀ X B}
                  → f S.≈ᵁ g → (W : S.Channel)
                  → T.prefix (F.₀ W) (G f) T.≈ℰ T.prefix (F.₀ W) (G g)
  image-component pres {f = f} {g} eq W = across′ (at-image′ f) (at-image′ g)
    (T.≈ℰ-cong-post _ (T.≈ℰ-cong-pre _ (pres (eq W))))

  covered-context : TestCoverage (StdUCMorphism 𝕄 𝕄′ ℰ ℰ′ F ν)
    → ∀ {A B X W} → ContextRepresentation W → {f g : A S.⇒ S.T₀ X B}
    → f S.≈ᵁ g → T.prefix W (G f) T.≈ℰ T.prefix W (G g)
  covered-context tests representation {f} {g} eq =
    across′ (conj′ (Mor._≅_.isoʳ iso) (G f)) (conj′ (Mor._≅_.isoʳ iso) (G g))
      (T.≈ℰ-cong-post _ (T.≈ℰ-cong-pre _ (image-component (covered-≈ℰ _ tests) eq source)))
    where open ContextRepresentation representation

  covered-≈ᵁ : TestCoverage (StdUCMorphism 𝕄 𝕄′ ℰ ℰ′ F ν) → AncillaCoverage → Preserves-≈ᵁ
  covered-≈ᵁ tests contexts eq W = covered-context tests (AncillaCoverage.represent contexts W) eq

  covered-≤UC : TestCoverage (StdUCMorphism 𝕄 𝕄′ ℰ ℰ′ F ν) → AncillaCoverage → Preserves-≤UC
  covered-≤UC tests contexts = transfer⁺ (covered-≈ᵁ tests contexts)

  -- Conjugation by the strong tensor comparisons can be cancelled before
  -- applying test injectivity; no stability of either observation is needed.
  reflects-≈ᵁ : PresheafMorphism.Mono ν → ∀ {A B X} {f g : A S.⇒ S.T₀ X B}
              → G f T.≈ᵁ G g → f S.≈ᵁ g
  reflects-≈ᵁ mono {f = f} {g} eq W = mono⇒reflects-≈ℰ mono
    (across′ (recover f) (recover g)
      (T.≈ℰ-cong-post _ (T.≈ℰ-cong-pre _ (eq (F.₀ W)))))
    where
    recover : ∀ {A B X} (h : A S.⇒ S.T₀ X B)
            → F.₁ (S.prefix W h) ≈ (Op.ψ ∘ Op.ψ ⊗₁ id) ∘ T.prefix (F.₀ W) (G h) ∘ Op.δ
    recover h = ⟺ (begin
      (Op.ψ ∘ Op.ψ ⊗₁ id) ∘ T.prefix (F.₀ W) (G h) ∘ Op.δ
        ≈⟨ refl⟩∘⟨ at-image′ h ⟩∘⟨refl ⟩
      (Op.ψ ∘ Op.ψ ⊗₁ id) ∘ ((Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ (S.prefix W h) ∘ Op.ψ) ∘ Op.δ
        ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ cancelʳ Op.ψδ)) ⟩
      (Op.ψ ∘ Op.ψ ⊗₁ id) ∘ (Op.δ ⊗₁ id ∘ Op.δ) ∘ F.₁ (S.prefix W h)
        ≈⟨ cancelˡ (assoc ○ (refl⟩∘⟨ cancelˡ
          (merge₁ˡ ○ (Op.ψδ ⟩⊗⟨refl) ○ ⊗.identity)) ○ Op.ψδ) ⟩
      F.₁ (S.prefix W h) ∎)

  record SimulatorRepresentation {X Y : S.Channel}
                                 (s′ : F.₀ Y ⇒ F.₀ X) (s : Y S.⇒ X)
                                 : Set (o′ ⊔ ℓ′ ⊔ cs ⊔ ℓs) where
    field action : ∀ {A B} (g : A ⇒ F.₀ Y ⊗₀ B) (W : T.Channel)
                 → T.prefix W (T.sub s′ ∘ g) T.≈ℰ T.prefix W (T.sub (F.₁ s) ∘ g)

  sub-image : ∀ {A B X Y} (s : Y S.⇒ X) (g : A S.⇒ S.T₀ Y B)
            → G (S.sub s S.∘ g) ≈ T.sub (F.₁ s) ∘ G g
  sub-image s g = (refl⟩∘⟨ F.homomorphism) ○ sym-assoc ○ (κ-sub s ⟩∘⟨refl) ○ assoc
    where open UCSetupMorphism (StdUCMorphism 𝕄 𝕄′ ℰ ℰ′ F ν) using (κ-sub)

  reflects-≤UC-witness : PresheafMorphism.Mono ν
    → ∀ {A B X Y} {f : A S.⇒ S.T₀ X B} {g : A S.⇒ S.T₀ Y B}
    → (s′ : F.₀ Y ⇒ F.₀ X) → G f T.≈ᵁ (T.sub s′ ∘ G g)
    → (s : Y S.⇒ X) → SimulatorRepresentation s′ s → f S.≤UC g
  reflects-≤UC-witness mono {g = g} s′ witness s representation = S.dummy-complete
    (s , reflects-≈ᵁ mono (T.≈ᵁ-trans witness
      (T.≈ᵁ-trans (SimulatorRepresentation.action representation (G g))
        (T.≈ᵁ-sym (T.≈C⇒≈ᵁ (sub-image s g))))))
