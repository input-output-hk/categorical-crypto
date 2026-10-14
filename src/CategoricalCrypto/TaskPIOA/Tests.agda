{-# OPTIONS --safe --without-K #-}

-- Operational witnesses and a perfectly secret one-bit masked-output resource.
-- The environment chooses the message adaptively; the residual word does not.
module CategoricalCrypto.TaskPIOA.Tests where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
import Data.Unit.Polymorphic as Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import CategoricalCrypto.TaskPIOA.Security
open import CategoricalCrypto.TaskPIOA.Setup
open import CategoricalCrypto.TaskPIOA.Simulation
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool; inv-pow-2)
open import ProbabilisticLogic.Distribution.Uniform.Flip using (uniform-not)

coinSignature : Finite → Signature
coinSignature I = record
  { inputs = I ; outputs = bit ; hidden = one ; tasks = bit
  ; taskOf = λ where (inj₁ _) → true ; (inj₂ _) → false
  ; task-inhabited = λ where false → inj₂ tt , refl ; true → inj₁ false , refl }

pattern waiting = inj₁ tt
pattern ready m = inj₂ (m , inj₁ tt)
pattern drawn m k = inj₂ (m , inj₂ k)
pattern ready′ = inj₂ (inj₁ tt)
pattern drawn′ c = inj₂ (inj₂ c)

real : Automaton (coinSignature bit)
real = record
  { states = one ⊕ (bit ⊠ (one ⊕ bit))
  ; initial = waiting
  ; input = λ where m waiting → return-ℚ (ready m) ; _ q → return-ℚ q
  ; choose = chooseReal
  ; owns = ownsReal
  ; kernel = λ where
      (inj₁ _) q → return-ℚ q
      (inj₂ _) (ready m) → Dmap (drawn m) uniform-Bool
      (inj₂ _) waiting → return-ℚ waiting
      (inj₂ _) (drawn m k) → return-ℚ (drawn m k)
  }
  where
  chooseReal : ⟨ one ⊕ (bit ⊠ (one ⊕ bit)) ⟩ → Bool → Maybe (Local (coinSignature bit))
  chooseReal waiting _ = nothing
  chooseReal (ready m) false = just (inj₂ tt)
  chooseReal (ready m) true = nothing
  chooseReal (drawn m k) false = nothing
  chooseReal (drawn m k) true = just (inj₁ (m xor k))
  ownsReal : ∀ q t a → chooseReal q t ≡ just a → taskOf (coinSignature bit) a ≡ t
  ownsReal waiting t a ()
  ownsReal (ready m) false a refl = refl
  ownsReal (ready m) true a ()
  ownsReal (drawn m k) false a ()
  ownsReal (drawn m k) true a refl = refl

ideal : Automaton (coinSignature bit)
ideal = record
  { states = one ⊕ (one ⊕ bit)
  ; initial = waiting
  ; input = λ where _ waiting → return-ℚ ready′ ; _ q → return-ℚ q
  ; choose = chooseIdeal
  ; owns = ownsIdeal
  ; kernel = λ where
      (inj₁ _) q → return-ℚ q
      (inj₂ _) ready′ → Dmap drawn′ uniform-Bool
      (inj₂ _) waiting → return-ℚ waiting
      (inj₂ _) (drawn′ c) → return-ℚ (drawn′ c)
  }
  where
  chooseIdeal : ⟨ one ⊕ (one ⊕ bit) ⟩ → Bool → Maybe (Local (coinSignature bit))
  chooseIdeal waiting _ = nothing
  chooseIdeal ready′ false = just (inj₂ tt)
  chooseIdeal ready′ true = nothing
  chooseIdeal (drawn′ c) false = nothing
  chooseIdeal (drawn′ c) true = just (inj₁ c)
  ownsIdeal : ∀ q t a → chooseIdeal q t ≡ just a → taskOf (coinSignature bit) a ≡ t
  ownsIdeal waiting t a ()
  ownsIdeal ready′ false a refl = refl
  ownsIdeal ready′ true a ()
  ownsIdeal (drawn′ c) false a ()
  ownsIdeal (drawn′ c) true a refl = refl

collapse : State real → State ideal
collapse waiting = waiting
collapse (ready m) = ready′
collapse (drawn m k) = drawn′ (m xor k)

xor-uniform : ∀ m → Dmap (m xor_) uniform-Bool ≈Mℚ uniform-Bool
xor-uniform false = Dmap-id uniform-Bool
xor-uniform true P = trans (lookupᴰℚ-Dmap (true xor_) uniform-Bool P) (sym (uniform-not P))

masked-simulation : Simulation real ideal
masked-simulation = record
  { stateMap = collapse ; starts = refl
  ; choices = λ where
      waiting _ → refl
      (ready m) false → refl
      (ready m) true → refl
      (drawn m k) false → refl
      (drawn m k) true → refl
  ; inputs-match = λ where
      m waiting → map-return collapse (ready m)
      m (ready n) → map-return collapse (ready n)
      m (drawn n k) → map-return collapse (drawn n k)
  ; local-match = λ where
      (inj₁ o) q → map-return collapse q
      (inj₂ h) waiting → map-return collapse waiting
      (inj₂ h) (drawn m k) → map-return collapse (drawn m k)
      (inj₂ h) (ready m) P → trans (sym (Dmap-∘ (drawn m) collapse uniform-Bool P))
        (trans (Dmap-∘ (m xor_) drawn′ uniform-Bool P)
          (map-cong drawn′ (Dmap (m xor_) uniform-Bool) uniform-Bool (xor-uniform m) P))
  }

masked-output-secure : resource real UC.≤UC resource ideal
masked-output-secure = simulation⇒≤UC masked-simulation

masked-output-contextual : real ≤₀ ideal
masked-output-contextual = resource-≤UC⇒contextual masked-output-secure

-- Sampling is hidden but its distribution survives into the repeated public
-- ciphertext, rather than being resampled independently on each send.
real-repeats : ∀ m k → runFrom real (true ∷ true ∷ []) (drawn m k)
  ≈Mℚ return-ℚ ((m xor k) ∷ (m xor k) ∷ [])
real-repeats m k P = refl

pulse : Automaton (coinSignature empty)
pulse = record
  { states = bit ; initial = false ; input = λ ()
  ; choose = λ where
      false false → just (inj₂ tt)
      false true → nothing
      true false → just (inj₂ tt)
      true true → just (inj₁ true)
  ; owns = λ where
      false false a refl → refl
      false true a ()
      true false a refl → refl
      true true a refl → refl
  ; kernel = λ where (inj₁ _) q → return-ℚ q ; (inj₂ _) _ → return-ℚ true
  }

disabled-then-enabled : traceDist pulse (true ∷ false ∷ true ∷ []) ≈Mℚ return-ℚ (true ∷ [])
disabled-then-enabled P = refl

repeated-task : traceDist pulse (false ∷ true ∷ true ∷ []) ≈Mℚ return-ℚ (true ∷ true ∷ [])
repeated-task P = refl

nonempty : ∀ {A : Set} → List A → ℚ
nonempty [] = 0ℚ
nonempty (_ ∷ _) = 1ℚ

two-events : ∀ {A : Set} → List A → ℚ
two-events (_ ∷ _ ∷ _) = 1ℚ
two-events _ = 0ℚ

disabled-does-not-stop : ¬ (traceDist pulse (true ∷ false ∷ true ∷ []) ≈Mℚ return-ℚ [])
disabled-does-not-stop e with e nonempty
... | ()

repetition-not-deduplication :
  ¬ (traceDist pulse (false ∷ true ∷ true ∷ []) ≈Mℚ traceDist pulse (false ∷ true ∷ []))
repetition-not-deduplication e with e two-events
... | ()

receiverSignature : Signature
receiverSignature = record
  { inputs = bit ; outputs = bit ; hidden = empty ; tasks = one
  ; taskOf = λ _ → tt ; task-inhabited = λ _ → inj₁ false , refl }

receiver : Automaton receiverSignature
receiver = record
  { states = bit ; initial = false ; input = λ b _ → return-ℚ b
  ; choose = λ b _ → just (inj₁ b)
  ; owns = λ _ _ _ _ → refl
  ; kernel = λ _ b → return-ℚ b }

wire : Wiring (coinSignature empty) receiverSignature empty
wire = record
  { left = record { name = λ () ; find = λ _ → nothing ; complete = λ () ; sound = λ _ _ () }
  ; right = record
    { name = inj₂ ; find = λ where (inj₁ ()) ; (inj₂ b) → just b
    ; complete = λ _ → refl ; sound = λ where (inj₁ ()) ; (inj₂ b) .b refl → refl }
  ; boundary-live = λ () }

network : Automaton (productSignature (coinSignature empty) receiverSignature empty)
network = product wire pulse receiver

send-first read-first : Schedule (productSignature (coinSignature empty) receiverSignature empty)
send-first = inj₁ false ∷ inj₁ true ∷ inj₂ tt ∷ []
read-first = inj₂ tt ∷ inj₁ false ∷ inj₁ true ∷ []

synchronized-product : traceDist network send-first ≈Mℚ return-ℚ (inj₁ true ∷ inj₂ true ∷ [])
synchronized-product P = refl

read-before-send : traceDist network read-first ≈Mℚ return-ℚ (inj₂ false ∷ inj₁ true ∷ [])
read-before-send P = refl

same-left-projection : leftSchedule send-first ≡ leftSchedule read-first
same-left-projection = refl

same-right-projection : rightSchedule send-first ≡ rightSchedule read-first
same-right-projection = refl

receiver-accepts : List (Bool ⊎ Bool) → ℚ
receiver-accepts [] = 0ℚ
receiver-accepts (inj₁ _ ∷ xs) = receiver-accepts xs
receiver-accepts (inj₂ false ∷ xs) = 0ℚ
receiver-accepts (inj₂ true ∷ xs) = 1ℚ

synchronization-not-interleaving-only :
  ¬ (traceDist network send-first ≈Mℚ return-ℚ (inj₁ true ∷ inj₂ false ∷ []))
synchronization-not-interleaving-only e with e receiver-accepts
... | ()

order-sensitive : ¬ (traceDist network send-first ≈Mℚ traceDist network read-first)
order-sensitive e with e receiver-accepts
... | ()

echoEnvironment : Environment (coinSignature bit)
echoEnvironment = record
  { signature = receiverSignature ; automaton = receiver
  ; wiring = record
    { left = echoPorts ; right = echoPorts ; boundary-live = λ () } }
  where
  echoPorts : Ports bit (empty ⊕ bit)
  echoPorts = record
    { name = inj₂ ; find = λ where (inj₁ ()) ; (inj₂ b) → just b
    ; complete = λ _ → refl ; sound = λ where (inj₁ ()) ; (inj₂ b) .b refl → refl }

adaptive-word : Schedule (productSignature (coinSignature bit) receiverSignature empty)
adaptive-word = inj₂ tt ∷ inj₁ false ∷ inj₁ true ∷ inj₂ tt ∷ inj₁ true ∷ []

adaptive-trace : Bool → List (Bool ⊎ Bool)
adaptive-trace c = inj₂ false ∷ inj₁ c ∷ inj₂ c ∷ inj₁ c ∷ []

masked-adaptive-law :
  observe real echoEnvironment adaptive-word ≈Mℚ Dmap adaptive-trace uniform-Bool
masked-adaptive-law P = refl

first-ciphertext : List (Bool ⊎ Bool) → ℚ
first-ciphertext [] = 0ℚ
first-ciphertext (inj₂ _ ∷ xs) = first-ciphertext xs
first-ciphertext (inj₁ false ∷ _) = 0ℚ
first-ciphertext (inj₁ true ∷ _) = 1ℚ

masked-ciphertext-fair :
  lookupᴰℚ (entries (observe real echoEnvironment adaptive-word)) first-ciphertext ≡ inv-pow-2 1
masked-ciphertext-fair = refl

masked-not-deterministic :
  ¬ (observe real echoEnvironment adaptive-word ≈Mℚ return-ℚ (adaptive-trace false))
masked-not-deterministic e with e first-ciphertext
... | ()

native-probabilistic-plugging :
  evaluate (pull (resource real) (pull Syntax.λ⇒
    (nativeTest echoEnvironment adaptive-word first-ciphertext))) Unit.tt ≡ inv-pow-2 1
native-probabilistic-plugging = refl
