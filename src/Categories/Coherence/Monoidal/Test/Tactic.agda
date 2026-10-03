------------------------------------------------------------------------
-- Tests for the reflection frontend of the monoidal coherence
-- solver: the manual call sites of
-- `Categories.Coherence.Monoidal.Test.Frontend`, with every
-- hand-written signature and DSL transcription replaced by
-- `solve-mor C`.

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Test.Tactic where

open import Level using (Level)
open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor using (Functor)

open import Categories.Coherence.Monoidal.Tactic

private variable
  o ℓ e : Level

module _ (C : MonoidalCategory o ℓ e) where
  open MonoidalCategory C

  module _ (A B : Obj)
           (μ : U [ A ⊗₀ A , A ])
           (η : U [ unit , A ])
           (s : U [ A , A ])
           (t : U [ B , B ]) where

    -- functoriality / id laws
    test-idˡ : U [ id ∘ s ≈ s ]
    test-idˡ = solve-mor C

    -- ∀-quantified goal: exercises the pi-prefix walk + weakening
    test-pi : ∀ (f : U [ A , B ]) (g : U [ B , A ]) → U [ (g ∘ f) ∘ id ≈ g ∘ f ]
    test-pi = solve-mor C

    test-assoc : U [ (s ∘ s) ∘ s ≈ s ∘ (s ∘ s) ]
    test-assoc = solve-mor C

    test-id⊗id : U [ id {A} ⊗₁ id {B} ≈ id ]
    test-id⊗id = solve-mor C

    -- interchange: disjoint boxes in either firing order
    test-swap : U [ (id ⊗₁ t) ∘ (s ⊗₁ id) ≈ (s ⊗₁ id) ∘ (id ⊗₁ t) ]
    test-swap = solve-mor C

    test-s-first : U [ (id ⊗₁ t) ∘ (s ⊗₁ id) ≈ s ⊗₁ t ]
    test-s-first = solve-mor C

    -- unitor/associator naturality through boxes
    test-ρ-nat : U [ unitorʳ.from ∘ (s ⊗₁ id) ≈ s ∘ unitorʳ.from ]
    test-ρ-nat = solve-mor C

    test-λ-nat : U [ unitorˡ.from ∘ (id ⊗₁ s) ≈ s ∘ unitorˡ.from ]
    test-λ-nat = solve-mor C

    test-α-nat : U [ associator.from ∘ ((s ⊗₁ t) ⊗₁ s) ≈ (s ⊗₁ (t ⊗₁ s)) ∘ associator.from ]
    test-α-nat = solve-mor C

    -- multi-wire and empty-domain generators
    test-α-nat-μ : U [ associator.from ∘ ((μ ⊗₁ t) ⊗₁ s) ≈ (μ ⊗₁ (t ⊗₁ s)) ∘ associator.from ]
    test-α-nat-μ = solve-mor C

    test-η-swap : U [ (η ⊗₁ id) ∘ (id ⊗₁ t) ≈ η ⊗₁ t ]
    test-η-swap = solve-mor C

    -- pure coherence (structural only, no generators)
    test-λ-iso : U [ unitorˡ.from ∘ unitorˡ.to ≈ id {A} ]
    test-λ-iso = solve-mor C

    -- as in the backend's own test suite, some structural leaves need
    -- their objects annotated in the STATEMENT: `_⊗₀_` is not
    -- injective for the unifier, so the goal's own implicits are
    -- otherwise unsolvable (the macro then blocks on them forever)
    test-triangle : U [ (id ⊗₁ unitorˡ.from) ∘ associator.from {A} {unit} {B}
                         ≈ unitorʳ.from {A} ⊗₁ id {B} ]
    test-triangle = solve-mor C

    test-pentagon
      : U [ (id ⊗₁ associator.from) ∘ associator.from ∘ (associator.from {A} {B} {A} ⊗₁ id {B})
             ≈ associator.from ∘ associator.from {A ⊗₀ B} {A} {B} ]
    test-pentagon = solve-mor C

    -- a derived tensor functor's action is the `_⊗₁_` node
    test-F₁ʳ : U [ Functor.F₁ (-⊗ B) s ≈ s ⊗₁ id ]
    test-F₁ʳ = solve-mor C

    test-F₁ˡ : U [ Functor.F₁ (B ⊗-) s ≈ id ⊗₁ s ]
    test-F₁ˡ = solve-mor C

    test-F₁-nat : U [ Functor.F₁ (-⊗ B) s ∘ (id ⊗₁ t) ≈ (id ⊗₁ t) ∘ (s ⊗₁ id) ]
    test-F₁-nat = solve-mor C
