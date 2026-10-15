{-# OPTIONS --safe --without-K #-}

-- Fixed source words forget activation silence, whereas native Tick replies
-- retain it. This is an observation-boundary separation, not a claim that
-- feedback alone increases distinguishing power: padded fixed words suffice.
module CategoricalCrypto.TaskPIOA.Adaptive where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.SSPAdapter
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Distribution.Uniform.Flip using (uniform-not)

pulseSignature : Signature
pulseSignature = record
  { inputs = empty ; outputs = one ; hidden = one ; tasks = one
  ; taskOf = λ _ → tt ; task-inhabited = λ _ → inj₁ tt , refl }

pattern start = inj₁ tt
pattern first b = inj₂ (inj₁ (b , inj₁ tt))
pattern second b = inj₂ (inj₁ (b , inj₂ (inj₁ tt)))
pattern third b = inj₂ (inj₁ (b , inj₂ (inj₂ tt)))
pattern stopped = inj₂ (inj₂ tt)

patternStates : Finite
patternStates = one ⊕ ((bit ⊠ (one ⊕ (one ⊕ one))) ⊕ one)

pulseAction : Bool → Maybe (Local pulseSignature)
pulseAction false = just (inj₂ tt)
pulseAction true = just (inj₁ tt)

patternMachine : Bool → Automaton pulseSignature
patternMachine flip = record
  { states = patternStates ; initial = start ; input = λ ()
  ; choose = λ where
      start _ → just (inj₂ tt)
      (first b) _ → pulseAction b
      (second b) _ → pulseAction (not b)
      (third b) _ → pulseAction (b xor flip)
      stopped _ → nothing
  ; owns = λ _ _ _ _ → refl
  ; kernel = λ where
      _ start → Dmap first uniform-Bool
      _ (first b) → return-ℚ (second b)
      _ (second b) → return-ℚ (third b)
      _ (third _) → return-ℚ stopped
      _ stopped → return-ℚ stopped }

alternating grouped : Automaton pulseSignature
alternating = patternMachine false
grouped = patternMachine true

private
  stopped-entries : ∀ flip ρ → entries (runFrom (patternMachine flip) ρ stopped)
    ≡ entries (return-ℚ [])
  stopped-entries flip [] = refl
  stopped-entries flip (tt ∷ ρ) rewrite stopped-entries flip ρ = refl

  truncate-entries : ∀ flip ρ →
    entries (traceDist (patternMachine flip) (tt ∷ tt ∷ tt ∷ tt ∷ ρ))
    ≡ entries (traceDist (patternMachine flip) (tt ∷ tt ∷ tt ∷ tt ∷ []))
  truncate-entries false ρ rewrite stopped-entries false ρ = refl
  truncate-entries true ρ rewrite stopped-entries true ρ = refl

-- The singleton task makes these cases exhaustive over ALL source schedules;
-- after the sampling activation and three pattern activations the tail stutters.
all-fixed-traces : (ρ : Schedule pulseSignature)
  → traceDist alternating ρ ≈Mℚ traceDist grouped ρ
all-fixed-traces [] ξ = refl
all-fixed-traces (tt ∷ []) ξ = refl
all-fixed-traces (tt ∷ tt ∷ []) ξ = refl
all-fixed-traces (tt ∷ tt ∷ tt ∷ []) ξ = refl
all-fixed-traces (tt ∷ tt ∷ tt ∷ tt ∷ ρ) ξ =
  trans (cong (λ es → lookupᴰℚ es ξ) (truncate-entries false ρ))
    (trans (uniform-not (λ where false → ξ (tt ∷ []) ; true → ξ (tt ∷ tt ∷ [])))
      (sym (cong (λ es → lookupᴰℚ es ξ) (truncate-entries true ρ))))

all-fixed-rewards : (ρ : Schedule pulseSignature) (reward : List ⊤ → ℚ)
  → lookupᴰℚ (entries (traceDist alternating ρ)) reward
    ≡ lookupᴰℚ (entries (traceDist grouped ρ)) reward
all-fixed-rewards = all-fixed-traces

all-scheduled-consumers : (ρ : Schedule pulseSignature) (verdict : List ⊤ → Bool)
  → experiment alternating ρ verdict ≈Mℚ experiment grouped ρ verdict
all-scheduled-consumers ρ verdict ξ = trans (experiment-agreement alternating ρ verdict ξ)
  (trans (>>=ᴹ-congʳ (return⊥ ∘ verdict) (traceDist alternating ρ)
    (traceDist grouped ρ) (all-fixed-traces ρ) ξ)
    (sym (experiment-agreement grouped ρ verdict ξ)))

present : Maybe ⊤ → Bool
present nothing = false
present (just _) = true

-- Stop immediately on a silent first pattern activation. Otherwise test the
-- third activation; its presence correlates with the first only in alternating.
adaptiveCalls : P.Calls (Tick pulseSignature) Bool
adaptiveCalls = P.call tt tt λ _ → P.call tt tt λ where
  nothing → P.ret false
  (just _) → P.call tt tt λ _ → P.call tt tt λ o → P.ret (present o)

paddedCalls : P.Calls (Tick pulseSignature) Bool
paddedCalls = P.call tt tt λ _ → P.call tt tt λ a →
  P.call tt tt λ _ → P.call tt tt λ c → P.ret (not (present a xor present c))

nativeConsumer : P.Calls (Tick pulseSignature) Bool → P.Protocol (Tick pulseSignature) Ωᴵ
nativeConsumer calls = record
  { St = ⊤ ; init = tt ; step = λ _ _ _ → P.mapᶜ (tt ,_) calls }

nativeExperiment : Automaton pulseSignature → P.Calls (Tick pulseSignature) Bool → Dist⊥ Bool
nativeExperiment M calls = runᵖ (nativeConsumer calls P.∘ᵖ resource M)
