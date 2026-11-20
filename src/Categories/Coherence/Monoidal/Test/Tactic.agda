------------------------------------------------------------------------
-- Tests for the reflection frontend of the monoidal coherence
-- solver: the manual call sites of
-- `Categories.Coherence.Monoidal.Test.Frontend`, with every
-- hand-written signature and DSL transcription replaced by
-- `solve-mor C`.

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Test.Tactic where

open import Level using (Level; _⊔_)
open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor using (Functor)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Categories.Coherence.Monoidal.Tactic

private variable
  o ℓ e : Level

module _ (C : MonoidalCategory o ℓ e) where
  private module MC = MonoidalCategory C
  open MC

  module _ (A B : MC.Obj)
           (μ : MC.U [ A ⊗₀ A , A ])
           (η : MC.U [ unit , A ])
           (s : MC.U [ A , A ])
           (t : MC.U [ B , B ]) where

    -- functoriality / id laws
    test-idˡ : MC.U [ id ∘ s ≈ s ]
    test-idˡ = solve-mor C

    -- ∀-quantified goal: exercises the pi-prefix walk + weakening
    test-pi : ∀ (f : MC.U [ A , B ]) (g : MC.U [ B , A ]) → MC.U [ (g ∘ f) ∘ id ≈ g ∘ f ]
    test-pi = solve-mor C

    test-assoc : MC.U [ (s ∘ s) ∘ s ≈ s ∘ (s ∘ s) ]
    test-assoc = solve-mor C

    test-id⊗id : MC.U [ id {A} ⊗₁ id {B} ≈ id ]
    test-id⊗id = solve-mor C

    -- interchange: disjoint boxes in either firing order
    test-swap : MC.U [ (id ⊗₁ t) ∘ (s ⊗₁ id) ≈ (s ⊗₁ id) ∘ (id ⊗₁ t) ]
    test-swap = solve-mor C

    test-s-first : MC.U [ (id ⊗₁ t) ∘ (s ⊗₁ id) ≈ s ⊗₁ t ]
    test-s-first = solve-mor C

    -- unitor/associator naturality through boxes
    test-ρ-nat : MC.U [ unitorʳ.from ∘ (s ⊗₁ id) ≈ s ∘ unitorʳ.from ]
    test-ρ-nat = solve-mor C

    test-λ-nat : MC.U [ unitorˡ.from ∘ (id ⊗₁ s) ≈ s ∘ unitorˡ.from ]
    test-λ-nat = solve-mor C

    test-α-nat : MC.U [ associator.from ∘ ((s ⊗₁ t) ⊗₁ s) ≈ (s ⊗₁ (t ⊗₁ s)) ∘ associator.from ]
    test-α-nat = solve-mor C

    -- multi-wire and empty-domain generators
    test-α-nat-μ : MC.U [ associator.from ∘ ((μ ⊗₁ t) ⊗₁ s) ≈ (μ ⊗₁ (t ⊗₁ s)) ∘ associator.from ]
    test-α-nat-μ = solve-mor C

    -- pure coherence (structural only, no generators)
    test-λ-iso : MC.U [ unitorˡ.from ∘ unitorˡ.to ≈ id {A} ]
    test-λ-iso = solve-mor C

    -- as in the backend's own test suite, some structural leaves need
    -- their objects annotated in the STATEMENT: `_⊗₀_` is not
    -- injective for the unifier, so the goal's own implicits are
    -- otherwise unsolvable (the macro then blocks on them forever)
    test-triangle : MC.U [ (id ⊗₁ unitorˡ.from) ∘ associator.from {A} {unit} {B}
                         ≈ unitorʳ.from {A} ⊗₁ id {B} ]
    test-triangle = solve-mor C

    test-pentagon
      : MC.U [ (id ⊗₁ associator.from) ∘ associator.from ∘ (associator.from {A} {B} {A} ⊗₁ id {B})
             ≈ associator.from ∘ associator.from {A ⊗₀ B} {A} {B} ]
    test-pentagon = solve-mor C

    -- a derived tensor functor's action IS the `_⊗₁_` node: mixed
    -- spellings must agree (regression for the `F₁`/`₁` occurrence
    -- parser; before it, the left sides atomised whole and never
    -- matched the literal composites)
    test-F₁ʳ : MC.U [ Functor.F₁ (-⊗ B) s ≈ s ⊗₁ id ]
    test-F₁ʳ = solve-mor C

    test-F₁ˡ : MC.U [ Functor.F₁ (B ⊗-) s ≈ id ⊗₁ s ]
    test-F₁ˡ = solve-mor C

    test-F₁-nat : MC.U [ Functor.F₁ (-⊗ B) s ∘ (id ⊗₁ t) ≈ (id ⊗₁ t) ∘ (s ⊗₁ id) ]
    test-F₁-nat = solve-mor C

    private
      endoSetoid : Setoid ℓ e
      endoSetoid = MC.hom-setoid {A} {A}

      pointwiseSetoid : Setoid ℓ (o ⊔ e)
      pointwiseSetoid = record
        { Carrier = MC.U [ A , A ]
        ; _≈_ = λ f g → ∀ (X : MC.Obj) → MC.U [ f ≈ g ]
        ; isEquivalence = record
          { refl = λ _ → Equiv.refl
          ; sym = λ p X → Equiv.sym (p X)
          ; trans = λ p q X → Equiv.trans (p X) (q X)
          }
        }

      reversedSetoid : Setoid ℓ e
      reversedSetoid = record
        { Carrier = MC.U [ A , A ]
        ; _≈_ = λ f g → MC.U [ g ≈ f ]
        ; isEquivalence = record
          { refl = Equiv.refl
          ; sym = Equiv.sym
          ; trans = λ p q → Equiv.trans q p
          }
        }

      delayed : ∀ {X : MC.Obj} → MC.U [ id {X} ≈ id ] → X Eq.≡ A → MC.U [ id {A} ≈ id ]
      delayed p Eq.refl = p

      delayedMorphism : ∀ {f : MC.U [ A , A ]}
                      → MC.U [ id ∘ f ≈ s ] → f Eq.≡ s → MC.U [ id ∘ s ≈ s ]
      delayedMorphism p Eq.refl = p

      delayedPair : ∀ {X : MC.Obj} → MC.U [ id {X} ≈ id ] → MC.U [ id {X} ≈ id ]
                  → X Eq.≡ A → MC.U [ id {A} ≈ id ]
      delayedPair p q Eq.refl = Equiv.trans p q

    test-setoid-alias : Setoid._≈_ endoSetoid (id ∘ s) s
    test-setoid-alias = solve-mor C

    -- A relation projection can expose binders or reorder its operands.
    test-setoid-pi : Setoid._≈_ pointwiseSetoid (id ∘ s) s
    test-setoid-pi = solve-mor C

    test-setoid-reversed : Setoid._≈_ reversedSetoid (id ∘ s) s
    test-setoid-reversed = solve-mor C

    -- The later argument determines the object of the earlier solver call.
    test-retry : MC.U [ id {A} ≈ id ]
    test-retry = delayed (solve-mor C) Eq.refl

    -- A resolved morphism meta must share the explicitly written atom's slot.
    test-morphism-retry : MC.U [ id ∘ s ≈ s ]
    test-morphism-retry = delayedMorphism (solve-mor C) Eq.refl

    test-shared-retries : MC.U [ id {A} ≈ id ]
    test-shared-retries = delayedPair (solve-mor C) (solve-mor C) Eq.refl
