{-# OPTIONS --safe --without-K #-}

-- The transfer of `_≈ℰ_` and `_≤UC_` along a `UCSetupMorphism`.

module CategoricalCrypto.Abstract2.Morphism where

open import Data.Product
open import Level
open import Relation.Nullary using (¬_)

open import Categories.Functor.Presheaf.Morphism
open import Categories.Functor.Properties

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup
open import CategoricalCrypto.UCSetup.Morphism

private variable
  o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs : Level

module Transfer {𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs}
                {𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs}
                (𝕄 : UCSetupMorphism 𝕊 𝕊′) where
  private
    module S = AbstractUC 𝕊
    module S′ = AbstractUC 𝕊′
  open UCSetupMorphism 𝕄

  -- The action on protocols
  G : ∀ {X A B} → A S.𝒞.⇒ S.T₀ X B → F.₀ A S′.𝒞.⇒ S′.T₀ (Φ.₀ X) (F.₀ B)
  G f = κ S′.𝒞.∘ F.₁ f

  Preserves-≈ℰ Reflects-≈ℰ : Set (o₁′ ⊔ ℓ₁′ ⊔ cs ⊔ ℓs)
  Preserves-≈ℰ = ∀ {A B} {f g : A S.𝒞.⇒ B} → f S.≈ℰ g → F.₁ f S′.≈ℰ F.₁ g
  Reflects-≈ℰ  = ∀ {A B} {f g : A S.𝒞.⇒ B} → F.₁ f S′.≈ℰ F.₁ g → f S.≈ℰ g

  Preserves-≤UC Reflects-≤UC : Set (o₁ ⊔ ℓ₁ ⊔ o₁′ ⊔ ℓ₁′ ⊔ o₂ ⊔ ℓ₂ ⊔ cs ⊔ ℓs)
  Preserves-≤UC = ∀ {A B X Y} {f : A S.𝒞.⇒ S.T₀ X B} {g : A S.𝒞.⇒ S.T₀ Y B}
                → f S.≤UC g → G f S′.≤UC G g
  Reflects-≤UC  = ∀ {A B X Y} {f : A S.𝒞.⇒ S.T₀ X B} {g : A S.𝒞.⇒ S.T₀ Y B}
                → G f S′.≤UC G g → f S.≤UC g

  epi⇒preserves-≈ℰ : ν.Epi → Preserves-≈ℰ
  epi⇒preserves-≈ℰ = epi⇒preserves ν

  mono⇒reflects-≈ℰ : ν.Mono → Reflects-≈ℰ
  mono⇒reflects-≈ℰ = mono⇒reflects ν

  module _ (epi : ν.Epi) (gs′ : S′.GradeStable) where

    transfer : Preserves-≤UC
    transfer {f = f} {g} f≤g = S′.dummy-complete (Φ.₁ s₀ , S′.bridge gs′ key)
      where
        s₀ = proj₁ (f≤g S.ℐ.id)

        dummy : f S.≈ᵁ S.sub s₀ S.𝒞.∘ g
        dummy = S.≈ᵁ-trans (S.≈ᵁ-sym (S.≈C⇒≈ᵁ (S.sub-identityˡ f)))
                           (proj₂ (f≤g S.ℐ.id))

        strict : κ S′.𝒞.∘ F.₁ (S.sub s₀ S.𝒞.∘ g) S′.𝒞.≈ S′.sub (Φ.₁ s₀) S′.𝒞.∘ G g
        strict = let open S′.𝒞 in
          (refl⟩∘⟨ F.homomorphism) ○ sym-assoc ○ (κ-sub s₀ ⟩∘⟨refl) ○ assoc

        key : G f S′.≈ℰ S′.sub (Φ.₁ s₀) S′.𝒞.∘ G g
        key = S′.≈ℰ-trans (S′.≈ℰ-cong-post κ (epi⇒preserves-≈ℰ epi (S.≈ᵁ⇒≈ℰ dummy)))
                          (S′.≈C⇒≈ℰ strict)

    -- The contrapositive: an impossibility proved downstream is an impossibility upstream
    transfer-impossible : ∀ {A B X Y} {f : A S.𝒞.⇒ S.T₀ X B} {g : A S.𝒞.⇒ S.T₀ Y B}
                        → ¬ (G f S′.≤UC G g) → ¬ (f S.≤UC g)
    transfer-impossible ng f≤g = ng (transfer f≤g)

  κ-Mono : Set (o₁ ⊔ o₁′ ⊔ o₂′ ⊔ ℓ₂′ ⊔ cs ⊔ ℓs)
  κ-Mono = ∀ {X B} {A : S′.𝒞.Obj} {h h′ : A S′.𝒞.⇒ F.₀ (S.T₀ X B)}
         → κ S′.𝒞.∘ h S′.≈ℰ κ S′.𝒞.∘ h′ → h S′.≈ℰ h′

  module _ (full : Full Φ.F) (κ-mono : κ-Mono)
           (mono : ν.Mono) (gs : S.GradeStable) where

    reflects-≤UC : Reflects-≤UC
    reflects-≤UC {f = f} {g} Gf≤Gg = S.dummy-complete (s , S.bridge gs key)
      where
        s′ = proj₁ (Gf≤Gg S′.ℐ.id)
        s = proj₁ (full s′)

        dummy : G f S′.≈ᵁ S′.sub (Φ.₁ s) S′.𝒞.∘ G g
        dummy = S′.≈ᵁ-trans (S′.≈ᵁ-sym (S′.≈C⇒≈ᵁ (S′.sub-identityˡ (G f))))
                  (S′.≈ᵁ-trans (proj₂ (Gf≤Gg S′.ℐ.id))
                    (S′.≈C⇒≈ᵁ (S′.𝒞.∘-resp-≈ˡ
                      (S′.sub-resp-≈ (S′.ℐ.Equiv.sym (proj₂ (full s′)))))))

        strict : S′.sub (Φ.₁ s) S′.𝒞.∘ G g S′.𝒞.≈ κ S′.𝒞.∘ F.₁ (S.sub s S.𝒞.∘ g)
        strict = let open S′.𝒞 in
          sym-assoc ○ (⟺ (κ-sub s) ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ F.homomorphism)

        key : f S.≈ℰ S.sub s S.𝒞.∘ g
        key = mono⇒reflects-≈ℰ mono
                (κ-mono (S′.≈ℰ-trans (S′.≈ᵁ⇒≈ℰ dummy) (S′.≈C⇒≈ℰ strict)))
