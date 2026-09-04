{-# OPTIONS --safe --without-K #-}

-- UC emulation, stated directly on the grading action.
--
-- A process carrying an adversary interface is a hom `A ⇒ X ⊛ B`; `f ≤UC g`
-- says a simulator `s : Y ⇒ X` turns the ideal `g` into something no
-- environment tells apart from the real `f`.  The reference arc reached the
-- same statement through a graded Kleisli category and its coherence-iso
-- regrading (`Abstract`/`Abstract2`, ~540 LOC); none of that tower is needed
-- for the four metatheorems, which are `sub`'s functoriality plus `_≈ℰ_`'s
-- congruence.
--
-- The dummy-adversary form is *equivalent* here, not merely implied: taking
-- `a := id` inverts `dummy-complete`.

import Categories.Morphism.Reasoning as MR

open import Data.Product.Base
open import Level

open import CategoricalCrypto.UC.Base

module CategoricalCrypto.UC.Emulation
  {o ℓ e os ℓs} (base : UCBase o ℓ e os ℓs) where

open import CategoricalCrypto.UC.Environment base public

open HomReasoning
open MR 𝒞

private variable A B′ C′ X X′ Y Y′ Z : Obj

infix 4 _≤UC_ _≤UC⁺_

_≤UC_ : {A B′ X Y : Obj} → A ⇒ X ⊛ B′ → A ⇒ Y ⊛ B′ → Set (o ⊔ ℓ ⊔ ℓs)
_≤UC_ {X = X} {Y} f g = Σ[ s ∈ Y ⇒ X ] f ≈ℰ (sub s ∘ g)

_≤UC⁺_ : {A B′ X Y : Obj} → A ⇒ X ⊛ B′ → A ⇒ Y ⊛ B′ → Set (o ⊔ ℓ ⊔ ℓs)
_≤UC⁺_ {X = X} {Y} f g =
  {Z : Obj} (a : X ⇒ Z) → Σ[ s ∈ Y ⇒ Z ] (sub a ∘ f) ≈ℰ (sub s ∘ g)

private
  merge : {X Y Z A : Obj} {t : Y ⇒ Z} {s : X ⇒ Y} {g : A ⇒ X ⊛ B′}
        → sub t ∘ (sub s ∘ g) ≈ sub (t ∘ s) ∘ g
  merge = sym-assoc ○ ∘-resp-≈ˡ (⟺ sub-∘)

≤UC-refl : {f : A ⇒ X ⊛ B′} → f ≤UC f
≤UC-refl = id , ≈ℰ-sym (≈⇒≈ℰ (elimˡ sub-id))

≤UC-trans : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} {h : A ⇒ Z ⊛ B′}
          → f ≤UC g → g ≤UC h → f ≤UC h
≤UC-trans (s , e) (t , d) =
  s ∘ t , ≈ℰ-trans e (≈ℰ-trans (≈ℰ-congˡ (sub s) d) (≈⇒≈ℰ merge))

dummy-complete : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} → f ≤UC g → f ≤UC⁺ g
dummy-complete (s , e) a = a ∘ s , ≈ℰ-trans (≈ℰ-congˡ (sub a) e) (≈⇒≈ℰ merge)

≤UC⁺⇒≤UC : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} → f ≤UC⁺ g → f ≤UC g
≤UC⁺⇒≤UC h with h id
... | s , e = s , ≈ℰ-trans (≈⇒≈ℰ (⟺ (elimˡ sub-id))) e

------------------------------------------------------------------------
-- Universal composition

-- Plugging one graded process on top of another: the lower one's adversary
-- interface bypasses the upper one, and the two are then merged.
infixr 9 _⊙_

_⊙_ : {A B′ C′ X X′ : Obj} → B′ ⇒ X′ ⊛ C′ → A ⇒ X ⊛ B′ → A ⇒ (X ⊛ X′) ⊛ C′
_⊙_ {X = X} h f = a⇒ ∘ T₁ X h ∘ f

-- Two simulators acting side by side: `sub` on the left factor, `T₁` on the
-- right.  This is the composite simulator `UC-compose` must produce.
_⊛₁_ : {X X′ Y Y′ : Obj} → Y ⇒ X → Y′ ⇒ X′ → Y ⊛ Y′ ⇒ X ⊛ X′
_⊛₁_ {X} s s′ = T₁ X s′ ∘ sub s

-- Monotonicity of `_⊙_` in both arguments.  Stated, not proved: the chain needs
-- two `Grading` laws this layer does not ask for — the `sub`/`T₁` interchange
-- (`sub s ∘ T₁ X f ≈ T₁ Y f ∘ sub s`, disjoint interfaces commute) and `a⇒`'s
-- naturality in its first two slots.  Both hold in any monoidal action; neither
-- is needed by anything above, so they are not fields until a consumer wants
-- this theorem.
UC-compose : Set (o ⊔ ℓ ⊔ ℓs)
UC-compose = {A B′ C′ X X′ Y Y′ : Obj}
             {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′}
             {h : B′ ⇒ X′ ⊛ C′} {k : B′ ⇒ Y′ ⊛ C′}
           → f ≤UC g → h ≤UC k → (h ⊙ f) ≤UC (k ⊙ g)
