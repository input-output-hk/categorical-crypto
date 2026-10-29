{-# OPTIONS --safe #-}

-- ============================================================================
-- `Machine.Trace.Compose` on toy machines: two counters side by side, a
-- counter split in two halves joined by a loop, and a counter behind `id`.
-- ============================================================================

module CategoricalCrypto.Examples.TraceCompose where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core using (Machine; MkMachine; MachineType; _⊗₁_; tr; _∘_; id)
open import CategoricalCrypto.Machine.Trace
open import CategoricalCrypto.Machine.Trace.Compose

Cmd : Channel
Cmd = ⊤ ⇿ ℕ

------------------------------------------------------------------------------
-- The counter of `Examples.TraceCounter`, checked on inputs

data _-⟦_/_⟧ᶜ_ : MachineType Cmd I ℕ where
  Inc : ∀ {n} → n -⟦ ϵ ⊗R ↑ᵢ tt / just (ϵ ⊗R ↑ₒ suc n) ⟧ᶜ suc n

Counter : Machine Cmd I
Counter = MkMachine _-⟦_/_⟧ᶜ_

-- Every input steps, so a checker needs no hint and never fails.
opaque
  unfolding _⊗₀_

  counter-step : ∀ s i → Step Counter s i
  counter-step _ (inj₁ tt) = step _ _ Inc

counter : Checker Counter
counter = record
  { Hint      = ⊤
  ; hintOf    = λ _ → tt
  ; Err       = λ _ _ _ → ⊥
  ; checkStep = λ _ i s → inj₂ (counter-step s i , refl)
  }

counter-complete : Complete Counter counter
counter-complete = record
  { refute = λ ()
  ; unique = λ { (step _ _ Inc , _) (step _ _ Inc , _) → refl }
  }

------------------------------------------------------------------------------
-- Two counters side by side

module Pair where

  open Verifier (Counter ⊗₁ Counter) (counter ⊗ᶜ counter)

  incₗ incᵣ : Input (Counter ⊗₁ Counter)
  incₗ = (ϵ ⊗R) ⊗R ↑ᵢ tt
  incᵣ = (L⊗ ϵ) ⊗R ↑ᵢ tt

  run : Trace → Maybe (List (Maybe (Output (Counter ⊗₁ Counter))))
  run es with verifyTrace (0 , 0) es
  ... | inj₁ _        = nothing
  ... | inj₂ (_ , vt) = just (outputs vt)

  opaque
    unfolding counter-step side

    -- Left, left, right: the left counter reaches 2, the right one 1.
    ok : run (⟨ inj₁ tt , incₗ ⟩ ∷ ⟨ inj₁ tt , incₗ ⟩ ∷ ⟨ inj₂ tt , incᵣ ⟩ ∷ [])
       ≡ just ( just ((ϵ ⊗R) ⊗R ↑ₒ 1) ∷ just ((ϵ ⊗R) ⊗R ↑ₒ 2) ∷ just ((L⊗ ϵ) ⊗R ↑ₒ 1) ∷ [])
    ok = refl

    -- A hint for the left counter on the right counter's input.
    mismatch : run (⟨ inj₁ tt , incᵣ ⟩ ∷ []) ≡ nothing
    mismatch = refl

------------------------------------------------------------------------------
-- A counter split in two halves joined by a loop
--
-- On `tt` the machine sends its state round the loop; when a value comes
-- back it answers with its successor and keeps that as the new state.
-- Closing the loop with `tr` gives the counter again, each step of which is
-- two steps of the halves.

Loop : Channel
Loop = ⊥ ⇿ ℕ

data _-⟦_/_⟧ˡ_ : MachineType (Cmd ⊗₀ Loop) (I ⊗₀ Loop) ℕ where
  Ask    : ∀ {n} → n -⟦ (ϵ ⊗R) ⊗R ↑ᵢ tt / just ((L⊗ ϵ) ⊗R ↑ₒ n) ⟧ˡ n
  Answer : ∀ {n m} → n -⟦ L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ m / just ((ϵ ⊗R) ⊗R ↑ₒ suc m) ⟧ˡ suc m

Halves : Machine (Cmd ⊗₀ Loop) (I ⊗₀ Loop)
Halves = MkMachine _-⟦_/_⟧ˡ_

opaque
  unfolding _⊗₀_

  halves-step : ∀ s i → Step Halves s i
  halves-step _ (inj₁ (inj₁ tt)) = step _ _ Ask
  halves-step _ (inj₂ (inj₂ n))  = step _ _ Answer

halves : Checker Halves
halves = record
  { Hint      = ⊤
  ; hintOf    = λ _ → tt
  ; Err       = λ _ _ _ → ⊥
  ; checkStep = λ _ i s → inj₂ (halves-step s i , refl)
  }

module Looped where

  open Verifier (tr Halves) (trᶜ halves)

  inc : Input (tr Halves)
  inc = ϵ ⊗R ↑ᵢ tt

  run : Trace → Maybe (List (Maybe (Output (tr Halves))))
  run es with verifyTrace 0 es
  ... | inj₁ _        = nothing
  ... | inj₂ (_ , vt) = just (outputs vt)

  -- Each step of the counter is an `Ask` followed by an `Answer`.
  two : List⁺ ⊤
  two = tt ∷ tt ∷ []

  opaque
    unfolding halves-step route

    ok : run (⟨ two , inc ⟩ ∷ ⟨ two , inc ⟩ ∷ [])
       ≡ just (just (ϵ ⊗R ↑ₒ 1) ∷ just (ϵ ⊗R ↑ₒ 2) ∷ [])
    ok = refl

    -- One hint is too few: the output of `Ask` goes round the loop.
    too-few : run (⟨ tt ∷ [] , inc ⟩ ∷ []) ≡ nothing
    too-few = refl

    -- Three are too many: the output of `Answer` leaves the loop.
    too-many : run (⟨ tt ∷ tt ∷ tt ∷ [] , inc ⟩ ∷ []) ≡ nothing
    too-many = refl

------------------------------------------------------------------------------
-- The counter behind an identity
--
-- A step of `Counter ∘ id` is three internal steps: `id` passes the `tt` up,
-- the counter answers, and `id` passes the answer down.  The hint names the
-- machine of each step: `inj₁` for `id`, `inj₂` for the counter.

module Composed where

  open Verifier (Counter ∘ id) (counter ∘ᶜ idᶜ)

  inc : Input (Counter ∘ id)
  inc = ϵ ⊗R ↑ᵢ tt

  run : Trace → Maybe (List (Maybe (Output (Counter ∘ id))))
  run es with verifyTrace (tt , 0) es
  ... | inj₁ _        = nothing
  ... | inj₂ (_ , vt) = just (outputs vt)

  through : List⁺ (⊤ ⊎ ⊤)
  through = inj₁ tt ∷ inj₂ tt ∷ inj₁ tt ∷ []

  opaque
    unfolding counter-step side route ∘σ-back

    ok : run (⟨ through , inc ⟩ ∷ ⟨ through , inc ⟩ ∷ [])
       ≡ just (just (ϵ ⊗R ↑ₒ 1) ∷ just (ϵ ⊗R ↑ₒ 2) ∷ [])
    ok = refl

    -- The counter cannot take the first step: the input arrives at `id`.
    out-of-order : run (⟨ inj₂ tt ∷ inj₁ tt ∷ inj₁ tt ∷ [] , inc ⟩ ∷ []) ≡ nothing
    out-of-order = refl

  -- Exact outputs need the representation of `_⊗₀_`.
  opaque
    unfolding _⊗₀_

    _≟O_ : DecidableEquality (Output (Counter ∘ id))
    inj₁ m ≟O inj₁ n with m ≟ℕ n
    ... | yes refl = yes refl
    ... | no m≢n   = no λ { refl → m≢n refl }

  -- Answering 2 first, which the counter cannot do.
  skip : List (Maybe (Output (Counter ∘ id)))
  skip = just (ϵ ⊗R ↑ₒ 2) ∷ []

  -- The composite checker is complete, so `passing?` decides whether any
  -- run with these hints answers 2 first: none does.
  opaque
    unfolding counter-step side route ∘σ-back _≟O_

    skips : ¬ Passing (∘ᶜ-complete counter-complete idᶜ-complete) (exactOutputs (Counter ∘ id) _≟O_)
                      (tt , 0) (⟨ through , inc ⟩ ∷ []) skip
    skips = toWitnessFalse
      {a? = passing? (∘ᶜ-complete counter-complete idᶜ-complete) (exactOutputs (Counter ∘ id) _≟O_)
                     (tt , 0) (⟨ through , inc ⟩ ∷ []) skip} tt
