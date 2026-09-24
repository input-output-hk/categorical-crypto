{-# OPTIONS --safe --without-K #-}

-- A graded monad read as a Kleisli triple, but with the monad's own
-- action and multiplication as `T₁`/`μ` in place of the triple's
-- derived `sub ρ⇒ ∘ ext u (return ∘ f)` / `ext u id`. These compute
-- better in some cases.

open import Level

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Monad.Graded

module Categories.Monad.Graded.FromMonad
  {o ℓ e o′ ℓ′ e′ : Level} {ℐ : MonoidalCategory o ℓ e} {𝒞 : Category o′ ℓ′ e′}
  (ℳ : GradedMonad ℐ 𝒞) where

open import Data.Product

open import Categories.Category.Monoidal.Utilities (MonoidalCategory.monoidal ℐ) using (module Shorthands)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation)

open Category 𝒞
open HomReasoning
open MR 𝒞

private
  module ℐ = MonoidalCategory ℐ
  module M = MonoidalFunctor ℳ
  module Mu (u : ℐ.Obj) = Functor (M.₀ u)
  open NaturalTransformation using (η; commute)

triple : GradedKleisliTriple ℐ 𝒞
triple = GradedMonad⇒GradedKleisliTriple ℳ

open GradedKleisliTriple triple public
  hiding ( T₁; T-identity; ext-T-fusion; T-homomorphism; T-resp-≈; return-commute
         ; μ; μ-commute; μ-identityˡ; μ-identityʳ; μ-assoc; sub-commute′; μ-sub-commute )

open Shorthands

private variable
  u v w u₁ u₂ v₁ v₂ : ℐ.Obj
  A B : Obj
  α β : u ℐ.⇒ v
  f g : A ⇒ B

T₁ : ∀ u {A B} → A ⇒ B → T₀ u A ⇒ T₀ u B
T₁ = Mu.F₁

μ : ∀ u v {A} → T₀ u (T₀ v A) ⇒ T₀ (u ℐ.⊗₀ v) A
μ u v {A} = η (η M.⊗-homo (u , v)) A

T-identity : T₁ u id ≈ id {T₀ u A}
T-identity {u} = Mu.identity u

T-homomorphism : T₁ u (f ∘ g) ≈ T₁ u f ∘ T₁ u g
T-homomorphism {u} = Mu.homomorphism u

T-resp-≈ : f ≈ g → T₁ u f ≈ T₁ u g
T-resp-≈ {u = u} = Mu.F-resp-≈ u

μT : (f : A ⇒ T₀ v B) → μ u v ∘ T₁ u f ≈ ext u f
μT _ = Equiv.refl

ext-T-fusion : ext u f ∘ T₁ u g ≈ ext u (f ∘ g)
ext-T-fusion = pullʳ (⟺ T-homomorphism)

return-commute : return ∘ f ≈ T₁ ℐ.unit f ∘ return
return-commute {f = f} = commute M.ε f

μ-commute : μ u v ∘ T₁ u (T₁ v f) ≈ T₁ (u ℐ.⊗₀ v) f ∘ μ u v
μ-commute {u} {v} {f = f} = commute (η M.⊗-homo (u , v)) f

μ-identityˡ : sub λ⇒ ∘ μ ℐ.unit u ∘ return ≈ id {T₀ u A}
μ-identityˡ = (refl⟩∘⟨ refl⟩∘⟨ introˡ T-identity) ○ M.unitaryˡ

μ-identityʳ : sub ρ⇒ ∘ μ u ℐ.unit ∘ T₁ u return ≈ id {T₀ u A}
μ-identityʳ = (refl⟩∘⟨ refl⟩∘⟨ ⟺ identityʳ) ○ M.unitaryʳ

μ-assoc : sub α⇒ {A} ∘ μ (u ℐ.⊗₀ v) w ∘ μ u v ≈ μ u (v ℐ.⊗₀ w) ∘ T₁ u (μ v w)
μ-assoc = (refl⟩∘⟨ refl⟩∘⟨ introˡ T-identity) ○ M.associativity ○ (refl⟩∘⟨ identityʳ) ○ (refl⟩∘⟨ identityʳ)

sub-commute′ : sub α ∘ T₁ u f ≈ T₁ v f ∘ sub α
sub-commute′ {α = α} {f = f} = commute (M.₁ α) f

μ-sub-commute : μ v₁ v₂ ∘ T₁ v₁ (sub β) ∘ sub α ≈ sub (α ℐ.⊗₁ β) ∘ μ u₁ u₂ {A}
μ-sub-commute {β = β} {α = α} = M.⊗-homo.commute (α , β)

sub-identityˡ : (f : B ⇒ T₀ u A) → sub ℐ.id ∘ f ≈ f
sub-identityˡ _ = elimˡ sub-identity
