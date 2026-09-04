{-# OPTIONS --safe --without-K #-}

-- The machine layer's hom equality: a state *simulation* (`_≲_`) rather than a
-- behavioural equality closing the state off at both ends.  A behavioural
-- equality relates machines whose state objects carry no morphism between them,
-- and then no base-level iteration law can discharge the ⊕-trace's congruence;
-- with simulations that congruence is an instance of the base's uniformity.
-- `_≲_` is reflexive and transitive but not symmetric, so the category's
-- equality is its equivalence closure
-- (`Categories.Category.EquivClosureHelper`).
--
-- The state map is drawn from `𝒫`, because that congruence spends uniformity
-- along it: see `Categories.Category.Monoidal.Pure`.  `𝒫` is a parameter of
-- this module alone, which is what keeps it out of the two coherence-only
-- modules (`Machines.Frame`, `Machines.Reassoc`).

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame

module CategoricalCrypto.Machines.Sim
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B : Obj

-- `θ` respects the point, the discard and the step, so `g` can run `f`'s state
-- through it.  This is the zig-zag generator of the machine equality.
record _≲_ {A B : Obj} (f g : Machine A B) : Set (ℓ ⊔ e) where
  field
    θ         : St f ⇒ St g
    θ-pure    : Pure θ
    θ-discard : discard (state g) ∘ θ ≈ discard (state f)
    θ-point   : θ ∘ point (state f) ≈ point (state g)
    θ-step    : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id

open _≲_ public

infix 4 _≲_ _≈ᴹ_

_≈ᴹ_ : Machine A B → Machine A B → Set (o ⊔ ℓ ⊔ e)
_≈ᴹ_ = EqC.EqClosure _≲_

-- The named-state form every proof in the layer is written in.
sim : {S T : State} {k : obj S ⊗₀ A ⇒ obj S ⊗₀ B} {k′ : obj T ⊗₀ A ⇒ obj T ⊗₀ B}
      (θ : obj S ⇒ obj T)
    → Pure θ → discard T ∘ θ ≈ discard S → θ ∘ point S ≈ point T
    → θ ⊗₁ id ∘ k ≈ k′ ∘ θ ⊗₁ id
    → mk S k ≲ mk T k′
sim θ q d p s = record { θ = θ ; θ-pure = q ; θ-discard = d ; θ-point = p ; θ-step = s }

-- Same state, `≈`-equal steps: the identity simulation.
mk-cong : {S : State} {k k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B} → k ≈ k′ → mk S k ≲ mk S k′
mk-cong eq = sim id pure-id identityʳ identityˡ
               (elimˡ ⊗.identity ○ eq ○ ⟺ (elimʳ ⊗.identity))

≲-refl : {f : Machine A B} → f ≲ f
≲-refl = mk-cong refl

≲-trans : {f g h : Machine A B} → f ≲ g → g ≲ h → f ≲ h
≲-trans s t = record
  { θ         = θ t ∘ θ s
  ; θ-pure    = pure-∘ (θ-pure t) (θ-pure s)
  ; θ-discard = pullˡ (θ-discard t) ○ θ-discard s
  ; θ-point   = pullʳ (θ-point s) ○ θ-point t
  ; θ-step    = (split₁ˡ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ θ-step s) ○ sym-assoc
              ○ (θ-step t ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ split₁ˡ)
  }

≈ᴹ-isEquivalence : IsEquivalence (_≈ᴹ_ {A} {B})
≈ᴹ-isEquivalence = EqC.isEquivalence _≲_

≲⇒≈ᴹ : {f g : Machine A B} → f ≲ g → f ≈ᴹ g
≲⇒≈ᴹ = EqC.return

≲⇒≈ᴹ˘ : {f g : Machine A B} → f ≲ g → g ≈ᴹ f
≲⇒≈ᴹ˘ s = EqC.symmetric _≲_ (EqC.return s)

infixr 9 _○ᴹ_

reflᴹ : {f : Machine A B} → f ≈ᴹ f
reflᴹ = IsEquivalence.refl ≈ᴹ-isEquivalence

⟺ᴹ : {f g : Machine A B} → f ≈ᴹ g → g ≈ᴹ f
⟺ᴹ = IsEquivalence.sym ≈ᴹ-isEquivalence

_○ᴹ_ : {f g h : Machine A B} → f ≈ᴹ g → g ≈ᴹ h → f ≈ᴹ h
_○ᴹ_ = IsEquivalence.trans ≈ᴹ-isEquivalence

------------------------------------------------------------------------
-- Collapsing a trivial state factor

collapseˡ : {S : State} {k : (unit ⊗₀ obj S) ⊗₀ A ⇒ (unit ⊗₀ obj S) ⊗₀ B}
            {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → λ⇒ ⊗₁ id ∘ k ≈ k′ ∘ λ⇒ ⊗₁ id → mk (Iˢ ⊛ S) k ≲ mk S k′
collapseˡ {S = S} = sim λ⇒ pure-λ⇒ (λ-discard S) (λ-point S)

collapseʳ : {S : State} {k : (obj S ⊗₀ unit) ⊗₀ A ⇒ (obj S ⊗₀ unit) ⊗₀ B}
            {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → ρ⇒ ⊗₁ id ∘ k ≈ k′ ∘ ρ⇒ ⊗₁ id → mk (S ⊛ Iˢ) k ≲ mk S k′
collapseʳ {S = S} = sim ρ⇒ pure-ρ⇒ (ρ-discard S) (ρ-point S)
