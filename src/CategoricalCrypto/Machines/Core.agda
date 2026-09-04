{-# OPTIONS --safe --without-K #-}

-- Mealy machines over a symmetric monoidal category, with *simulation* as the
-- hom equality.
--
-- The base structure used is exactly: a symmetric monoidal `𝒱` for pairing
-- states, plus a point and a discard on each state object.  No monad appears —
-- a monad's strength and commutativity are what make its Kleisli category
-- symmetric monoidal, and that is all the construction consumes.
--
-- Hom equality is a state *simulation* (`_≲_`) rather than a behavioural
-- equality closing the state off at both ends.  A behavioural equality relates
-- machines whose state objects carry no morphism between them, and then no
-- base-level iteration law can discharge the ⊕-trace's congruence; with
-- simulations that congruence is an instance of the base's uniformity.  `_≲_`
-- is reflexive and transitive but not symmetric, so the category's equality is
-- its equivalence closure (`Categories.Category.EquivClosureHelper`).

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Construct.Closure.Equivalence as EqC

module CategoricalCrypto.Machines.Core {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B P Q R X Y : Obj

-- Swaps the second and third state factor; its own inverse.
swp : (P ⊗₀ Q) ⊗₀ R ⇒ (P ⊗₀ R) ⊗₀ Q
swp = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

------------------------------------------------------------------------
-- Machines

-- A state object comes with a point (the initial state) and a discard.  Both
-- are real data at the instances that matter: in a Kleisli category `unit` is
-- neither initial nor terminal, so `point` is a possibly-effectful initial
-- state, and a degenerate `discard` annihilates every trace.  Imposing
-- affineness on `𝒱` is what would make `discard` canonical.
record State : Set (o ⊔ ℓ) where
  field
    obj     : Obj
    point   : unit ⇒ obj
    discard : obj ⇒ unit

open State public

Iˢ : State
Iˢ = record { obj = unit ; point = id ; discard = id }

infixr 9 _⊛_

_⊛_ : State → State → State
S ⊛ T = record
  { obj     = obj S ⊗₀ obj T
  ; point   = point S ⊗₁ point T ∘ λ⇐
  ; discard = λ⇒ ∘ discard S ⊗₁ discard T
  }

record Machine (A B : Obj) : Set (o ⊔ ℓ) where
  field
    state : State

  St : Obj
  St = obj state

  field
    step : St ⊗₀ A ⇒ St ⊗₀ B

open Machine public

mk : (S : State) → obj S ⊗₀ A ⇒ obj S ⊗₀ B → Machine A B
mk S k = record { state = S ; step = k }

------------------------------------------------------------------------
-- The ways a step can act on a paired state

-- The left factor of a paired state acts on the whole interface.
onL : (P ⊗₀ X ⇒ P ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onL k = swp ∘ k ⊗₁ id ∘ swp

-- The right factor of a paired state acts on the whole interface.
onR : (Q ⊗₀ X ⇒ Q ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onR k = α⇐ ∘ id ⊗₁ k ∘ α⇒

-- `onR` with the codomain state freed, hence definitionally `onR` wherever
-- both apply; the general form accepts a state braiding.
onRᵍ : (Q ⊗₀ X ⇒ R ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ R) ⊗₀ Y
onRᵍ k = α⇐ ∘ id ⊗₁ k ∘ α⇒

------------------------------------------------------------------------
-- Composition

idᴹ : Machine A A
idᴹ = mk Iˢ id

infixr 9 _∘ᴹ_

_∘ᴹ_ : Machine B P → Machine A B → Machine A P
g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))

------------------------------------------------------------------------
-- Simulation, and the hom equality it generates

-- `θ` respects the point, the discard and the step, so `g` can run `f`'s state
-- through it.  This is the zig-zag generator of the machine equality.
record _≲_ {A B : Obj} (f g : Machine A B) : Set (ℓ ⊔ e) where
  field
    θ         : St f ⇒ St g
    θ-discard : discard (state g) ∘ θ ≈ discard (state f)
    θ-point   : θ ∘ point (state f) ≈ point (state g)
    θ-step    : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id

open _≲_ public

infix 4 _≲_ _≈ᴹ_

_≈ᴹ_ : Machine A B → Machine A B → Set (o ⊔ ℓ ⊔ e)
_≈ᴹ_ = EqC.EqClosure _≲_

-- The named-state form every proof below is written in.
sim : {S T : State} {k : obj S ⊗₀ A ⇒ obj S ⊗₀ B} {k′ : obj T ⊗₀ A ⇒ obj T ⊗₀ B}
      (θ : obj S ⇒ obj T)
    → discard T ∘ θ ≈ discard S → θ ∘ point S ≈ point T
    → θ ⊗₁ id ∘ k ≈ k′ ∘ θ ⊗₁ id
    → mk S k ≲ mk T k′
sim θ d p s = record { θ = θ ; θ-discard = d ; θ-point = p ; θ-step = s }

-- Same state, `≈`-equal steps: the identity simulation.
mk-cong : {S : State} {k k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B} → k ≈ k′ → mk S k ≲ mk S k′
mk-cong eq = sim id identityʳ identityˡ
               (elimˡ ⊗.identity ○ eq ○ ⟺ (elimʳ ⊗.identity))

≲-refl : {f : Machine A B} → f ≲ f
≲-refl = mk-cong refl

≲-trans : {f g h : Machine A B} → f ≲ g → g ≲ h → f ≲ h
≲-trans s t = record
  { θ         = θ t ∘ θ s
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
