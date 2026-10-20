{-# OPTIONS --safe #-}

-- ============================================================================
-- `Machine.Trace` on a toy machine: a counter that, on every `tt` from its
-- lower interface, increments its state and answers with the new value.
-- ============================================================================

module CategoricalCrypto.Examples.TraceCounter where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core using (Machine; MkMachine; MachineType)
open import CategoricalCrypto.Machine.Trace

Cmd : Channel
Cmd = ⊤ ⇿ ℕ

data _-⟦_/_⟧ᶜ_ : MachineType Cmd I ℕ where
  Inc : ∀ {n} → n -⟦ ϵ ⊗R ↑ᵢ tt / just (ϵ ⊗R ↑ₒ suc n) ⟧ᶜ suc n

Counter : Machine Cmd I
Counter = MkMachine _-⟦_/_⟧ᶜ_

data Msg : Type where
  inc : Msg

embed : Msg → Input Counter
embed inc = ϵ ⊗R ↑ᵢ tt

-- Exact outputs need the representation of `_⊗₀_`.
opaque
  unfolding _⊗₀_

  _≟O_ : DecidableEquality (Output Counter)
  inj₁ m ≟O inj₁ n with m ≟ℕ n
  ... | yes refl = yes refl
  ... | no m≢n   = no λ { refl → m≢n refl }

-- Steps are deterministic, so no hint is needed.
checkable : Checkable Counter
checkable = record
  { Hint      = ⊤
  ; hintOf    = λ _ → tt
  ; Msg       = Msg
  ; embed     = embed
  ; Err       = λ _ _ _ → ⊥
  ; checkStep = λ where _ inc _ → inj₂ (step _ _ Inc , refl)
  }

complete-counter : Complete Counter checkable
complete-counter = record
  { refute = λ ()
  ; unique = λ { (step _ _ Inc , _) (step _ _ Inc , _) → refl }
  }

open Verifier Counter checkable (exactOutputs Counter _≟O_)

-- Three increments from 0, answering 1, 2 and 3.
good : Trace
good = ⟨ tt , inc , just (ϵ ⊗R ↑ₒ 1) ⟩
     ∷ ⟨ tt , inc , just (ϵ ⊗R ↑ₒ 2) ⟩
     ∷ ⟨ tt , inc , just (ϵ ⊗R ↑ₒ 3) ⟩
     ∷ []

-- The same, but claiming the counter skipped 2.
bad : Trace
bad = ⟨ tt , inc , just (ϵ ⊗R ↑ₒ 1) ⟩
    ∷ ⟨ tt , inc , just (ϵ ⊗R ↑ₒ 3) ⟩
    ∷ []

isOk : ∀ {s es} → TraceErr s es ⊎ Σ[ s′ ∈ ℕ ] ValidTrace s es s′ → Bool
isOk (inj₁ _) = false
isOk (inj₂ _) = true

-- Running the verifier needs `_≟O_` to compute.
opaque
  unfolding _≟O_

  good-ok : isOk (verifyTrace 0 good) ≡ true
  good-ok = refl

  bad-fails : isOk (verifyTrace 0 bad) ≡ false
  bad-fails = refl

  -- `bad` is not just rejected by the checker: no run of the counter fits it.
  bad-impossible : ¬ (Σ[ s′ ∈ ℕ ] ValidTrace 0 bad s′)
  bad-impossible = toWitnessFalse {a? = validTrace? complete-counter 0 bad} tt
