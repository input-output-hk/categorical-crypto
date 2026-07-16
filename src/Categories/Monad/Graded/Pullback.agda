{-# OPTIONS --safe --without-K #-}

-- Pullback of a graded Kleisli triple ℳ over ℐ along a lax monoidal functor
-- Φ : 𝒥 → ℐ (restriction of scalars).

module Categories.Monad.Graded.Pullback where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.Monad.Graded
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e oⱼ ℓⱼ eⱼ o′ ℓ′ e′ : Level}
  {𝒞 : Category o′ ℓ′ e′} {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} {ℐ : MonoidalCategory o ℓ e}
  (Φ : MonoidalFunctor 𝒥 ℐ) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module 𝒥 = MonoidalCategory 𝒥
    module ℐ = MonoidalCategory ℐ
    module Φ = MonoidalFunctor Φ
  open GradedKleisliTriple ℳ

  Φ₀ = Φ.F₀
  Φ₁ = Φ.F₁

  pullbackM : GradedMonad ℐ 𝒞 → GradedMonad 𝒥 𝒞
  pullbackM GM = ∘-Monoidal GM Φ

  pullback : GradedKleisliTriple 𝒥 𝒞
  pullback = GradedMonad⇒GradedKleisliTriple (pullbackM (GradedKleisliTriple⇒GradedMonad ℳ))

  private module R = GradedKleisliTriple pullback

  -- Extensional recovery of the pulled-back fields
  --
  -- `R.T₀ u A ≡ T₀ (Φ₀ u) A`, `R.sub α ≡ sub (Φ₁ α)` and `R.return ≡ sub Φ.ε ∘
  -- return` all hold definitionally; only `ext` unfolds to
  -- the μ∘T₁ form and needs the ext-T-fusion of ℳ to reach the ext pasting.

  pullback-sub : ∀ {u v} (α : 𝒥.U [ u , v ]) {A} → 𝒞 [ R.sub α {A} ≈ sub (Φ₁ α) ]
  pullback-sub α = 𝒞.Equiv.refl

  pullback-return : ∀ {A} → 𝒞 [ R.return {A} ≈ sub Φ.ε 𝒞.∘ return ]
  pullback-return = 𝒞.Equiv.refl

  pullback-ext : ∀ {u v A B} (f : 𝒞 [ A , T₀ (Φ₀ v) B ])
               → 𝒞 [ R.ext u f ≈ sub (Φ.⊗-homo.η (u , v)) 𝒞.∘ ext (Φ₀ u) f ]
  pullback-ext {u} f = let open 𝒞.HomReasoning in
    𝒞.assoc ○ (refl⟩∘⟨ (ext-T-fusion ○ ext-resp-≈ 𝒞.identityˡ))

-- Pullback along the identity recovers ℳ
module _ {o ℓ e o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (ℐ : MonoidalCategory o ℓ e) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module R = GradedKleisliTriple (pullback (idF-Monoidal ℐ) ℳ)
  open GradedKleisliTriple ℳ
  open MR 𝒞

  pullback-id-return : ∀ {A} → 𝒞 [ R.return {A} ≈ return ]
  pullback-id-return = elimˡ sub-identity

  pullback-id-ext : ∀ {u v A B} (f : 𝒞 [ A , T₀ v B ]) → 𝒞 [ R.ext u f ≈ ext u f ]
  pullback-id-ext f = let open 𝒞.HomReasoning in
    pullback-ext (idF-Monoidal ℐ) ℳ f ○ elimˡ sub-identity

-- Iterated pullback along Ψ then Φ agrees with pullback along Φ∘Ψ
module _ {o ℓ e oⱼ ℓⱼ eⱼ oₖ ℓₖ eₖ o′ ℓ′ e′ : Level}
  (𝒞 : Category o′ ℓ′ e′) (𝒦 : MonoidalCategory oₖ ℓₖ eₖ)
  (𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ) (ℐ : MonoidalCategory o ℓ e)
  (Ψ : MonoidalFunctor 𝒦 𝒥) (Φ : MonoidalFunctor 𝒥 ℐ) (ℳ : GradedKleisliTriple ℐ 𝒞)
  where
  private
    module 𝒞 = Category 𝒞
    module Φ = MonoidalFunctor Φ
    module Ψ = MonoidalFunctor Ψ
    ℳΦ = pullback Φ ℳ
    module R² = GradedKleisliTriple (pullback Ψ ℳΦ)
    module R∘ = GradedKleisliTriple (pullback (∘-Monoidal Φ Ψ) ℳ)
  open GradedKleisliTriple ℳ
  open MR 𝒞

  pullback-∘-return : ∀ {A} → 𝒞 [ R².return {A} ≈ R∘.return ]
  pullback-∘-return = 𝒞.Equiv.sym (pushˡ sub-homomorphism)

  pullback-∘-ext : ∀ {u v A B} (f : 𝒞 [ A , T₀ (Φ.F₀ (Ψ.F₀ v)) B ])
                 → 𝒞 [ R².ext u f ≈ R∘.ext u f ]
  pullback-∘-ext f = let open 𝒞.HomReasoning in
    pullback-ext Ψ ℳΦ f
      ○ (refl⟩∘⟨ pullback-ext Φ ℳ f)
      ○ pullˡ (⟺ sub-homomorphism)
      ○ ⟺ (pullback-ext (∘-Monoidal Φ Ψ) ℳ f)
