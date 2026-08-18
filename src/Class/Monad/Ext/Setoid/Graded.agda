{-# OPTIONS --safe --without-K #-}

-- A `SetoidMonad` is a monad on `Setoids`, so — unlike a `MonadSetoid` — it is
-- an honest endofunctor, and at the trivial grading a `GradedMonad`.  That makes
-- a `SetoidMonadMorphism` a `GradedMonadMorphism`, which is what the note on
-- `MonadMorphismSetoid` says the carrier-indexed equality cannot deliver.

open import Level

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext.Setoid

open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal.Properties using (idF-Monoidal)
import Categories.Monad as C
open import Categories.Monad.Construction.Kleisli using (KleisliTriple; Kleisli⇒Monad)
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism using (Components; IsGradedKleisliMorphism)
open import Categories.Monad.Graded.Trivial
open import Categories.Monad.Graded.Uncurried using (GradedMonadMorphism; toMonadMorphism)
open import Categories.Monad.Relative using (RMonad⇒Functor)
open import Function.Bundles using (_⟨$⟩_)

module Class.Monad.Ext.Setoid.Graded where

private variable ℓ oᵢ ℓᵢ eᵢ : Level

module _ (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : SetoidMonad M ⦄ ⦃ _ : SetoidMonadLaws M ⦄ where

  SetoidMonad-KleisliTriple : KleisliTriple (Setoids ℓ ℓ)
  SetoidMonad-KleisliTriple = record
    { F₀        = ≈ˢ-setoid
    ; unit      = λ {S} → returnˢ {S = S}
    ; extend    = λ {S} {S′} → bindˢ {S = S} {S′ = S′}
    ; identityʳ = λ {S} {S′} → >>=-identityˡ-≈ˢ {S = S} {S′}
    ; identityˡ = λ {S} {m} → >>=-identityʳ-≈ˢ {S = S} m
    ; assoc     = λ {S} {S′} {S″} → ≈ˢ.sym {S = S″} (>>=-assoc-≈ˢ {S = S} {S′} {S″} _)
    ; sym-assoc = λ {S} {S′} {S″} → >>=-assoc-≈ˢ {S = S} {S′} {S″} _
    ; extend-≈  = λ {S} {S′} {k} {h} k≈h →
        bindˢ-cong {S = S} {S′ = S′} {f = k} {g = h} (λ _ → k≈h) (≈ˢ.refl {S = S})
    }

  -- `F₁` is `_<$>ᴹ_` and `F-resp-≈` is `<$>ᴹ-congˢ-f`.
  SetoidMonad-Functor : Endofunctor (Setoids ℓ ℓ)
  SetoidMonad-Functor = RMonad⇒Functor SetoidMonad-KleisliTriple

  SetoidMonad-Monad : C.Monad (Setoids ℓ ℓ)
  SetoidMonad-Monad = Kleisli⇒Monad _ SetoidMonad-KleisliTriple

  SetoidMonad-GradedKleisliTriple : GradedKleisliTriple (Oneᴹ {oᵢ} {ℓᵢ} {eᵢ}) (Setoids ℓ ℓ)
  SetoidMonad-GradedKleisliTriple = ungraded SetoidMonad-KleisliTriple

  SetoidMonad-GradedMonad : GradedMonad (Oneᴹ {oᵢ} {ℓᵢ} {eᵢ}) (Setoids ℓ ℓ)
  SetoidMonad-GradedMonad = GradedKleisliTriple⇒GradedMonad SetoidMonad-GradedKleisliTriple

module _ {ℓ oᵢ ℓᵢ eᵢ : Level} (M N : Type↑)
  ⦃ _ : Monad M ⦄ ⦃ _ : SetoidMonad M ⦄ ⦃ _ : SetoidMonadLaws M ⦄
  ⦃ _ : Monad N ⦄ ⦃ _ : SetoidMonad N ⦄ ⦃ _ : SetoidMonadLaws N ⦄
  (Θ : SetoidMonadMorphism M N) where

  private
    module Θ = SetoidMonadMorphism Θ

    Kᴹ = SetoidMonad-KleisliTriple M {ℓ = ℓ}
    Kᴺ = SetoidMonad-KleisliTriple N {ℓ = ℓ}

    θᶜ : Components (ungraded Kᴹ {oᵢ} {ℓᵢ} {eᵢ}) (ungraded Kᴺ) idF (idF-Monoidal Oneᴹ)
    θᶜ {A = S} = Θ.θˢ {S = S}

  SetoidMonadMorphism-IsGradedKleisliMorphism :
    IsGradedKleisliMorphism (ungraded Kᴹ {oᵢ} {ℓᵢ} {eᵢ}) (ungraded Kᴺ) idF
                            (idF-Monoidal Oneᴹ) θᶜ
  SetoidMonadMorphism-IsGradedKleisliMorphism =
    ungraded-morphism Kᴹ Kᴺ idF θᶜ
      (λ {S} {a} → Θ.θ-return {S = S} a)
      (λ {S} {S′} f {m} → Θ.θ-bind {S = S} {S′ = S′} m (f ⟨$⟩_))

  SetoidMonadMorphism-GradedMonadMorphism :
    GradedMonadMorphism (SetoidMonad-GradedMonad M {oᵢ} {ℓᵢ} {eᵢ} {ℓ})
                        (SetoidMonad-GradedMonad N {oᵢ} {ℓᵢ} {eᵢ} {ℓ})
                        idF (idF-Monoidal Oneᴹ)
  SetoidMonadMorphism-GradedMonadMorphism =
    toMonadMorphism (ungraded Kᴹ) (ungraded Kᴺ) idF (idF-Monoidal Oneᴹ)
                    SetoidMonadMorphism-IsGradedKleisliMorphism
