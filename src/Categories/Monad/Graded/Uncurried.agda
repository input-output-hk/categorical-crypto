{-# OPTIONS --safe --without-K #-}

-- The uncurried view of a graded monad, and its morphisms.
--
-- A graded monad is a lax monoidal functor ℐ → End 𝒞; uncurrying it
-- we get ℐ × 𝒞 → 𝒞. A morphism of graded monads across (F , Φ) is
-- then a 2-cell
--
--     κ̂ : F ∘ uncurry ℳ ⇒ uncurry ℳ′ ∘ (Φ × F)
--
-- compatible with the unit and the multiplication.
--
-- `toMonadMorphism`/`toKleisliMorphism` prove that over the same component
-- family κ this is the same data as the Kleisli-triple form
-- `IsGradedKleisliMorphism`: for the backward direction that κ is `κ̂`'s own
-- component family is the *index* of `toKleisliMorphism`'s type; forward,
-- `toMonadMorphism-κ` states it.
--
-- A potential TODO for later: a graded monad is really just a lax
-- functor Bℐ → Cat (classically a monad is a lax functor 1 → Cat),
-- and so a morphism of graded monads is just a morphism in the lax
-- slice category, i.e. a natural transformation ℳ ⇒ ℳ′ ∘ BΦ.

module Categories.Monad.Graded.Uncurried where

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Category.Product
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Monad.Graded
import Categories.Monad.Graded.Ext as GradedExt
open import Categories.Monad.Graded.Morphism
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation

open Functor using () renaming (F₀ to _$₀_; F₁ to _$₁_)
open NaturalTransformation

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ o ℓ e o′ ℓ′ e′ : Level}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ} {ℐ′ : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′}
  (ℳ : GradedMonad ℐ 𝒞) (ℳ′ : GradedMonad ℐ′ 𝒞′)
  (F : Functor 𝒞 𝒞′) (Φ : MonoidalFunctor ℐ ℐ′)
  where
  private
    module 𝒞′ = Category 𝒞′
    module ℳ = MonoidalFunctor ℳ
    module ℳ′ = MonoidalFunctor ℳ′
    module F = Functor F
    module Φ = MonoidalFunctor Φ

  record GradedMonadMorphism : Set (oᵢ ⊔ ℓᵢ ⊔ o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    no-eta-equality
    field
      κ̂ : NaturalTransformation (F ∘F uncurry.₀ ℳ.F) (uncurry.₀ ℳ′.F ∘F (Φ.F ⁂ F))

    module κ̂ = NaturalTransformation κ̂

    κ : ∀ {X A} → 𝒞′ [ F.₀ (ℳ.₀ X $₀ A) , ℳ′.₀ (Φ.₀ X) $₀ F.₀ A ]
    κ {X} {A} = κ̂.η (X , A)

    field
      κ̂-unit : ∀ {A} → 𝒞′ [ κ 𝒞′.∘ F.₁ (η ℳ.ε A)
                          ≈ η (ℳ′.₁ Φ.ε) (F.₀ A) 𝒞′.∘ η ℳ′.ε (F.₀ A) ]
      κ̂-mult : ∀ {X Y A}
             → 𝒞′ [ κ 𝒞′.∘ F.₁ (η (ℳ.⊗-homo.η (X , Y)) A)
                  ≈ η (ℳ′.₁ (Φ.⊗-homo.η (X , Y))) (F.₀ A)
                      𝒞′.∘ η (ℳ′.⊗-homo.η (Φ.₀ X , Φ.₀ Y)) (F.₀ A)
                      𝒞′.∘ ℳ′.₀ (Φ.₀ X) $₁ κ 𝒞′.∘ κ ]

------------------------------------------------------------------------
-- Kleisli-triple form ⟺ 2-cell form
------------------------------------------------------------------------

module _ {oᵢ ℓᵢ eᵢ oⱼ ℓⱼ eⱼ o ℓ e o′ ℓ′ e′ : Level}
  {ℐ : MonoidalCategory oᵢ ℓᵢ eᵢ} {ℐ′ : MonoidalCategory oⱼ ℓⱼ eⱼ}
  {𝒞 : Category o ℓ e} {𝒞′ : Category o′ ℓ′ e′}
  (ℳ : GradedKleisliTriple ℐ 𝒞) (ℳ′ : GradedKleisliTriple ℐ′ 𝒞′)
  (F : Functor 𝒞 𝒞′) (Φ : MonoidalFunctor ℐ ℐ′)
  where
  private
    module ℐ = MonoidalCategory ℐ
    module ℐ′ = MonoidalCategory ℐ′
    module 𝒞 = Category 𝒞
    module 𝒞′ = Category 𝒞′
    module ℳ = GradedKleisliTriple ℳ
    module ℳ′ = GradedKleisliTriple ℳ′
    module Ext = GradedExt ℳ
    module Ext′ = GradedExt ℳ′
    module F = Functor F
    module Φ = MonoidalFunctor Φ
    module MR𝒞 = MR 𝒞
    open MonoidalUtilities.Shorthands ℐ.monoidal using (ρ⇒)
    open MonoidalUtilities.Shorthands ℐ′.monoidal using () renaming (ρ⇒ to ρ⇒′)
    open 𝒞′.HomReasoning
    open MR 𝒞′

    variable
      X Y : ℐ.Obj
      A B : 𝒞.Obj

  ℳ̂ : GradedMonad ℐ 𝒞
  ℳ̂ = GradedKleisliTriple⇒GradedMonad ℳ

  ℳ̂′ : GradedMonad ℐ′ 𝒞′
  ℳ̂′ = GradedKleisliTriple⇒GradedMonad ℳ′

  module _ {κ : Components ℳ ℳ′ F Φ} (m : IsGradedKleisliMorphism ℳ ℳ′ F Φ κ) where
    open IsGradedKleisliMorphism m

    κ-T₁ : (f : 𝒞 [ A , B ])
         → 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.T₁ X f) ≈ ℳ′.T₁ (Φ.₀ X) (F.₁ f) 𝒞′.∘ κ ]
    κ-T₁ {X = X} f = begin
        κ 𝒞′.∘ F.₁ (ℳ.sub ρ⇒ 𝒞.∘ ℳ.ext X (ℳ.return 𝒞.∘ f))
          ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
        κ 𝒞′.∘ F.₁ (ℳ.sub ρ⇒) 𝒞′.∘ F.₁ (ℳ.ext X (ℳ.return 𝒞.∘ f))
          ≈⟨ pullˡ (κ-sub ρ⇒) ○ 𝒞′.assoc ⟩
        ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ κ 𝒞′.∘ F.₁ (ℳ.ext X (ℳ.return 𝒞.∘ f))
          ≈⟨ refl⟩∘⟨ κ-ext (ℳ.return 𝒞.∘ f) ⟩
        ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ ℳ′.sub H
          𝒞′.∘ ℳ′.ext (Φ.₀ X) (κ 𝒞′.∘ F.₁ (ℳ.return 𝒞.∘ f)) 𝒞′.∘ κ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ℳ′.ext-resp-≈ unitPart ⟩∘⟨refl ⟩
        ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ ℳ′.sub H
          𝒞′.∘ ℳ′.ext (Φ.₀ X) (ℳ′.sub Φ.ε 𝒞′.∘ pure) 𝒞′.∘ κ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ℳ′.sub-commute₂ ⟩∘⟨refl ⟩
        ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ ℳ′.sub H
          𝒞′.∘ (ℳ′.sub (ℐ′.id ℐ′.⊗₁ Φ.ε) 𝒞′.∘ ℳ′.ext (Φ.₀ X) pure) 𝒞′.∘ κ
          ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ 𝒞′.assoc) ○ (refl⟩∘⟨ 𝒞′.sym-assoc) ○ 𝒞′.sym-assoc ⟩
        (ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ ℳ′.sub H 𝒞′.∘ ℳ′.sub (ℐ′.id ℐ′.⊗₁ Φ.ε))
          𝒞′.∘ (ℳ′.ext (Φ.₀ X) pure 𝒞′.∘ κ)
          ≈⟨ subs ⟩∘⟨refl ⟩
        ℳ′.sub ρ⇒′ 𝒞′.∘ (ℳ′.ext (Φ.₀ X) pure 𝒞′.∘ κ)
          ≈⟨ 𝒞′.sym-assoc ⟩
        ℳ′.T₁ (Φ.₀ X) (F.₁ f) 𝒞′.∘ κ ∎
      where
        H    = Φ.⊗-homo.η (X , ℐ.unit)
        pure = ℳ′.return 𝒞′.∘ F.₁ f

        unitPart : 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.return 𝒞.∘ f) ≈ ℳ′.sub Φ.ε 𝒞′.∘ pure ]
        unitPart = (refl⟩∘⟨ F.homomorphism) ○ pullˡ κ-return ○ 𝒞′.assoc

        subs : 𝒞′ [ ℳ′.sub (Φ.₁ ρ⇒) 𝒞′.∘ ℳ′.sub H 𝒞′.∘ ℳ′.sub (ℐ′.id ℐ′.⊗₁ Φ.ε)
                  ≈ ℳ′.sub ρ⇒′ ]
        subs = ⟺ (ℳ′.sub-homomorphism ○ (refl⟩∘⟨ ℳ′.sub-homomorphism))
             ○ ℳ′.sub-resp-≈ Φ.unitaryʳ

    toMonadMorphism : GradedMonadMorphism ℳ̂ ℳ̂′ F Φ
    toMonadMorphism = record
      { κ̂ = ntHelper record
        { η       = λ where (_ , _) → κ
        ; commute = λ where
            (φ , f) → begin
              κ 𝒞′.∘ F.₁ (ℳ.T₁ _ f 𝒞.∘ ℳ.sub φ)
                ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
              κ 𝒞′.∘ F.₁ (ℳ.T₁ _ f) 𝒞′.∘ F.₁ (ℳ.sub φ)
                ≈⟨ pullˡ (κ-T₁ f) ○ 𝒞′.assoc ⟩
              ℳ′.T₁ _ (F.₁ f) 𝒞′.∘ κ 𝒞′.∘ F.₁ (ℳ.sub φ)
                ≈⟨ refl⟩∘⟨ κ-sub φ ⟩
              ℳ′.T₁ _ (F.₁ f) 𝒞′.∘ ℳ′.sub (Φ.₁ φ) 𝒞′.∘ κ
                ≈⟨ 𝒞′.sym-assoc ⟩
              (ℳ′.T₁ _ (F.₁ f) 𝒞′.∘ ℳ′.sub (Φ.₁ φ)) 𝒞′.∘ κ ∎
        }
      ; κ̂-unit = κ-return
      ; κ̂-mult = κ-ext 𝒞.id
               ○ (refl⟩∘⟨ (ℳ′.ext-resp-≈ (elimʳ F.identity) ⟩∘⟨refl))
               ○ (refl⟩∘⟨ (⟺ (Ext′.μT κ) ⟩∘⟨refl))
               ○ (refl⟩∘⟨ 𝒞′.assoc)
      }

  module _ (n : GradedMonadMorphism ℳ̂ ℳ̂′ F Φ) where
    open GradedMonadMorphism n

    private
      nat-ℐ : (c : X ℐ.⇒ Y)
            → 𝒞′ [ κ {Y} {A} 𝒞′.∘ F.₁ (ℳ.sub c) ≈ ℳ′.sub (Φ.₁ c) 𝒞′.∘ κ ]
      nat-ℐ c = (refl⟩∘⟨ F.F-resp-≈ (𝒞.Equiv.sym (MR𝒞.elimˡ ℳ.T-identity)))
              ○ κ̂.commute (c , 𝒞.id)
              ○ (elimˡ (ℳ′.T-resp-≈ F.identity ○ ℳ′.T-identity) ⟩∘⟨refl)

      nat-𝒞 : (f : 𝒞 [ A , B ])
            → 𝒞′ [ κ 𝒞′.∘ F.₁ (ℳ.T₁ X f) ≈ ℳ′.T₁ (Φ.₀ X) (F.₁ f) 𝒞′.∘ κ ]
      nat-𝒞 f = (refl⟩∘⟨ F.F-resp-≈ (𝒞.Equiv.sym (MR𝒞.elimʳ ℳ.sub-identity)))
              ○ κ̂.commute (ℐ.id , f)
              ○ (elimʳ (ℳ′.sub-resp-≈ Φ.identity ○ ℳ′.sub-identity) ⟩∘⟨refl)

    toKleisliMorphism : IsGradedKleisliMorphism ℳ ℳ′ F Φ κ
    toKleisliMorphism = record
      { κ-return = κ̂-unit
      ; κ-ext    = λ {X} {Y} f → begin
          κ 𝒞′.∘ F.₁ (ℳ.ext X f)
            ≈⟨ refl⟩∘⟨ F.F-resp-≈ (𝒞.Equiv.sym (Ext.μT f)) ⟩
          κ 𝒞′.∘ F.₁ (ℳ.μ X Y 𝒞.∘ ℳ.T₁ X f)
            ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
          κ 𝒞′.∘ F.₁ (ℳ.μ X Y) 𝒞′.∘ F.₁ (ℳ.T₁ X f)
            ≈⟨ pullˡ κ̂-mult ⟩
          (ℳ′.sub (Φ.⊗-homo.η (X , Y)) 𝒞′.∘ ℳ′.μ (Φ.₀ X) (Φ.₀ Y)
             𝒞′.∘ ℳ′.T₁ (Φ.₀ X) κ 𝒞′.∘ κ) 𝒞′.∘ F.₁ (ℳ.T₁ X f)
            ≈⟨ 𝒞′.assoc ○ (refl⟩∘⟨ 𝒞′.assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ 𝒞′.assoc) ⟩
          ℳ′.sub (Φ.⊗-homo.η (X , Y)) 𝒞′.∘ ℳ′.μ (Φ.₀ X) (Φ.₀ Y)
            𝒞′.∘ ℳ′.T₁ (Φ.₀ X) κ 𝒞′.∘ κ 𝒞′.∘ F.₁ (ℳ.T₁ X f)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ nat-𝒞 f ⟩
          ℳ′.sub (Φ.⊗-homo.η (X , Y)) 𝒞′.∘ ℳ′.μ (Φ.₀ X) (Φ.₀ Y)
            𝒞′.∘ ℳ′.T₁ (Φ.₀ X) κ 𝒞′.∘ ℳ′.T₁ (Φ.₀ X) (F.₁ f) 𝒞′.∘ κ
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ ℳ′.T-homomorphism) ⟩
          ℳ′.sub (Φ.⊗-homo.η (X , Y)) 𝒞′.∘ ℳ′.μ (Φ.₀ X) (Φ.₀ Y)
            𝒞′.∘ ℳ′.T₁ (Φ.₀ X) (κ 𝒞′.∘ F.₁ f) 𝒞′.∘ κ
            ≈⟨ refl⟩∘⟨ pullˡ (Ext′.μT (κ 𝒞′.∘ F.₁ f)) ⟩
          ℳ′.sub (Φ.⊗-homo.η (X , Y))
            𝒞′.∘ ℳ′.ext (Φ.₀ X) (κ 𝒞′.∘ F.₁ f) 𝒞′.∘ κ ∎
      ; κ-sub    = nat-ℐ
      }

  toMonadMorphism-κ : {κ : Components ℳ ℳ′ F Φ} (m : IsGradedKleisliMorphism ℳ ℳ′ F Φ κ)
                    → GradedMonadMorphism.κ (toMonadMorphism m) {X} {A} ≡ κ
  toMonadMorphism-κ _ = refl
