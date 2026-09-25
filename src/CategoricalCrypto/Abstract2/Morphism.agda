{-# OPTIONS --safe --without-K #-}

-- Transport of `_≈ℰ_` and `_≤UC_` between setups: along a `UCSetupMorphism`,
-- and — where 𝒞, ℐ and ℳ are shared and only the observation moves — along a
-- refinement of the bare kernel alone.

module CategoricalCrypto.Abstract2.Morphism where

open import Data.Product
open import Level
open import Relation.Nullary using (¬_)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.Functor.Properties

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup
open import CategoricalCrypto.UCSetup.Morphism

private variable
  o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs cs′ ℓs′ : Level

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
        s₀    = proj₁ (S.≤UC⇒dummy f≤g)
        dummy = proj₂ (S.≤UC⇒dummy f≤g)

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

------------------------------------------------------------------------
-- One computational structure, two observations
------------------------------------------------------------------------

reobserve : (𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs)
          → Presheaf (UCSetup.𝒞 𝕊) (Setoids cs′ ℓs′)
          → UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs′ ℓs′
reobserve 𝕊 ℰ′ = record { 𝒞 = 𝒞 ; ℐ = ℐ ; ℳ = ℳ ; ℰ = ℰ′ } where open UCSetup 𝕊

-- Unlike `Transfer`, the compared morphisms are the ORIGINAL ones, so no
-- `GradeStable` and no epi/mono hypothesis is spent: `_≈ᵁ_` is the bare kernel
-- read at the prefix contexts `μ ∘ T₁`, which both readings share, and the
-- order then crosses by the dummy-adversary theorem with its simulator
-- unchanged.  Instantiated at both family bridges, `UC.Family.Quantitative`
-- and `UC.Family.Negligible.Quantitative`.
module Refine (𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs)
              (ℰ′ : Presheaf (UCSetup.𝒞 𝕊) (Setoids cs′ ℓs′))
              (refineℰ : {A B : Category.Obj (UCSetup.𝒞 𝕊)}
                         {f g : UCSetup.𝒞 𝕊 [ A , B ]}
                       → UCSetup._≈ℰ_ 𝕊 f g → UCSetup._≈ℰ_ (reobserve 𝕊 ℰ′) f g)
              where
  private
    module S  = AbstractUC 𝕊
    module S′ = AbstractUC (reobserve 𝕊 ℰ′)

    variable
      A B : S.𝒞.Obj
      X Y : S.ℐ.Obj

  ≈ᵁ-refine : {f g : A S.𝒞.⇒ S.T₀ X B} → f S.≈ᵁ g → f S′.≈ᵁ g
  ≈ᵁ-refine h W = refineℰ (h W)

  ≤UC-refine : {f : A S.𝒞.⇒ S.T₀ X B} {g : A S.𝒞.⇒ S.T₀ Y B} → f S.≤UC g → f S′.≤UC g
  ≤UC-refine le = let s , h = S.≤UC⇒dummy le in S′.dummy-complete (s , ≈ᵁ-refine h)
