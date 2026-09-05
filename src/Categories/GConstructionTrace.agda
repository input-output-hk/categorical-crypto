{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The wiring and the trace algebra the G construction runs on: the
-- structural morphisms `β`, `α`, `γ` of a G-composite's loop body, and
-- the three consequences of the trace hypotheses that its laws need.
--
-- All of this was `where`-local to `Categories.GConstruction`'s category
-- literal; the monoidal layer needs the same lemmas, so it lives here
-- instead.  `right-superposing` is the mirror of `Traced.superposing`
-- and is the one that needs a coherence step (`RS`, solved in
-- `Categories.GConstructionIdentityCoherence`).
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced

module Categories.GConstructionTrace
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

open import Categories.Category.Monoidal.Bundle

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionIdentityCoherence as GCohId

private
  module C where
    open Category C public
    open Traced Traced public
    open U.Shorthands Monoidal public
    open import Categories.Category.Monoidal.Reasoning Monoidal public
      using (refl⟩⊗⟨_)
    open import Categories.Morphism.Reasoning C public using (introˡ; pullʳ; elimʳ)
    open BProps.Shorthands braided public

  Cˢ : SymmetricMonoidalCategory a b c
  Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

open C.HomReasoning

-- β swaps the last two factors: (A ⊗ Y) ⊗ X → (A ⊗ X) ⊗ Y
β : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (P C.⊗₀ R) C.⊗₀ Q
β = C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

-- The two coherence isomorphisms of the G-construction composition: `α`
-- routes the two loop ends together after the factors have acted, `γ`
-- feeds them in.
α : ∀ {A⁻ B⁺ B⁻ C⁺ : C.Obj} →
    (B⁻ C.⊗₀ C⁺) C.⊗₀ (A⁻ C.⊗₀ B⁺) C.⇒ (A⁻ C.⊗₀ C⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
α = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id) C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒

γ : ∀ {A⁺ B⁺ B⁻ C⁻ : C.Obj} →
    (A⁺ C.⊗₀ C⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) C.⇒ (B⁺ C.⊗₀ C⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)
γ = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id)
  C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒ C.∘ C.id C.⊗₁ C.σ⇒

module WithTrace
  (trace-resp-≈ : ∀ {X A B} {f g : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                  f C.≈ g → C.trace f C.≈ C.trace g)
  (trace-∘ˡ : ∀ {X A B B'} {g : B C.⇒ B'} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
              g C.∘ C.trace f C.≈ C.trace (g C.⊗₁ C.id C.∘ f))
  (trace-∘ʳ : ∀ {X A A' B} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} {h : A' C.⇒ A} →
              C.trace f C.∘ h C.≈ C.trace (f C.∘ h C.⊗₁ C.id))
  (trace-comm : ∀ {X Y A B} {f : (A C.⊗₀ X) C.⊗₀ Y C.⇒ (B C.⊗₀ X) C.⊗₀ Y} →
                C.trace (C.trace f) C.≈ C.trace (C.trace (β C.∘ f C.∘ β)))
  where

  -- trace of the yanking core: β at Q = R = X swaps the loop wire with a
  -- parallel copy of itself, so its trace is the identity.
  trace-βyank : ∀ {Y X : C.Obj} → C.trace (β {Y} {X} {X}) C.≈ C.id
  trace-βyank = C.superposing ○ (C.refl⟩⊗⟨ C.yanking) ○ C.⊗.identity

  -- framed yanking: a loop whose body is a yanking core followed by
  -- loop-independent processing g collapses to g.
  trace-gyank : ∀ {Y X B' : C.Obj} {g : Y C.⊗₀ X C.⇒ B'} →
                C.trace (g C.⊗₁ C.id C.∘ β {Y} {X} {X}) C.≈ g
  trace-gyank = ⟺ trace-∘ˡ ○ C.elimʳ trace-βyank

  -- Right superposing, the mirror of `Traced.superposing`.
  right-superposing : ∀ {X Y A' B'} {f' : A' C.⊗₀ X C.⇒ B' C.⊗₀ X} →
    C.trace f' C.⊗₁ C.id {Y} C.≈ C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
  right-superposing {X} {Y} {A'} {B'} {f'} = begin
    C.trace f' C.⊗₁ C.id
      ≈⟨ braiding-swap ⟩
    C.σ⇒ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
      ≈⟨ refl⟩∘⟨ C.Equiv.sym C.superposing ⟩∘⟨refl ⟩
    C.σ⇒ C.∘ C.trace (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒
      ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
    C.σ⇒ C.∘ C.trace ((C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
      ≈⟨ trace-∘ˡ ⟩
    C.trace (C.σ⇒ C.⊗₁ C.id C.∘ (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
      ≈⟨ trace-resp-≈ (GCohId.Transport.WithGen.RS Cˢ A' B' X X Y f') ⟩
    C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
    ∎
    where -- introduce σ⇒ ∘ σ⇒ ≈ id on the left, then braiding naturality
          braiding-swap : C.trace f' C.⊗₁ C.id C.≈
            C.σ⇒ {Y} {B'} C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
          braiding-swap = C.introˡ C.commutative
                        ○ C.pullʳ (C.braiding.⇒.commute _)
