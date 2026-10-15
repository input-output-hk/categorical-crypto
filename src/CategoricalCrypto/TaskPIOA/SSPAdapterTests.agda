{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.SSPAdapterTests where

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_)
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _/_)
open import Data.Rational.Properties using (_≤?_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import CategoricalCrypto.SSP.Dist.Kernel using (_>>=ᶜ_)
open import CategoricalCrypto.SSP.Observation using (evalC)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import CategoricalCrypto.TaskPIOA.SSPAdapter
import CategoricalCrypto.TaskPIOA.Tests as Source
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)

private
  lift-return : ∀ {A B : Set} (μ : Dist-ℚ A) (x : A) (f : A → B)
    → μ ≈Mℚ return-ℚ x → (μ >>=ᴹ λ a → return⊥ (f a)) ≈Mℚ return⊥ (f x)
  lift-return μ x f law ξ = trans
    (>>=ᴹ-congʳ (λ a → return⊥ (f a)) μ (return-ℚ x) law ξ)
    (>>=ᴹ-identityˡ x (λ a → return⊥ (f a)) ξ)

accept-receiver : List (Bool ⊎ Bool) → Bool
accept-receiver [] = false
accept-receiver (inj₁ _ ∷ xs) = accept-receiver xs
accept-receiver (inj₂ b ∷ xs) = b

native-send-first : experiment Source.network Source.send-first accept-receiver ≈Mℚ return⊥ true
native-send-first ξ = trans (experiment-agreement Source.network Source.send-first accept-receiver ξ)
  (lift-return (traceDist Source.network Source.send-first)
    (inj₁ true ∷ inj₂ true ∷ []) accept-receiver Source.synchronized-product ξ)

native-read-first : experiment Source.network Source.read-first accept-receiver ≈Mℚ return⊥ false
native-read-first ξ = trans (experiment-agreement Source.network Source.read-first accept-receiver ξ)
  (lift-return (traceDist Source.network Source.read-first)
    (inj₂ false ∷ inj₁ true ∷ []) accept-receiver Source.read-before-send ξ)

native-order-sensitive : ¬ (experiment Source.network Source.send-first accept-receiver
  ≈Mℚ experiment Source.network Source.read-first accept-receiver)
native-order-sensitive e with e (maybeℚ (λ where false → 0ℚ ; true → 1ℚ))
... | ()

module Network = Synchronized Source.wire Source.pulse Source.receiver

synchronized-send-first : Network.native Source.send-first (false , false)
  ≈Mℚ return⊥ (inj₁ true ∷ inj₂ true ∷ [])
synchronized-send-first ξ = trans (Network.schedule-compatibility Source.send-first (false , false) ξ)
  (lift-return (traceDist Source.network Source.send-first)
    (inj₁ true ∷ inj₂ true ∷ []) (λ xs → xs) Source.synchronized-product ξ)

synchronized-read-first : Network.native Source.read-first (false , false)
  ≈Mℚ return⊥ (inj₂ false ∷ inj₁ true ∷ [])
synchronized-read-first ξ = trans (Network.schedule-compatibility Source.read-first (false , false) ξ)
  (lift-return (traceDist Source.network Source.read-first)
    (inj₂ false ∷ inj₁ true ∷ []) (λ xs → xs) Source.read-before-send ξ)

accept-pulse : List Bool → Bool
accept-pulse [] = false
accept-pulse (b ∷ _) = b

native-disabled-then-enabled : experiment Source.pulse (true ∷ false ∷ true ∷ []) accept-pulse
  ≈Mℚ return⊥ true
native-disabled-then-enabled ξ = trans
  (experiment-agreement Source.pulse (true ∷ false ∷ true ∷ []) accept-pulse ξ)
  (lift-return (traceDist Source.pulse (true ∷ false ∷ true ∷ []))
    (true ∷ []) accept-pulse Source.disabled-then-enabled ξ)

native-disabled-stutter : evalC (P.step (resource Source.pulse) false true tt)
  ≈Mℚ return⊥ (false , nothing)
native-disabled-stutter = native-disabled Source.pulse false true refl

correlated : Automaton (Source.coinSignature empty)
correlated = record
  { states = bit ; initial = false ; input = λ ()
  ; choose = λ where b false → just (inj₂ tt) ; b true → just (inj₁ b)
  ; owns = λ where b false a refl → refl ; b true a refl → refl
  ; kernel = λ where (inj₂ _) _ → uniform-Bool ; (inj₁ _) b → return-ℚ b }

repeat-word : Schedule (Source.coinSignature empty)
repeat-word = false ∷ true ∷ true ∷ []

same-pair : List Bool → Bool
same-pair (false ∷ false ∷ []) = true
same-pair (true ∷ true ∷ []) = true
same-pair _ = false

first : List Bool → Bool
first (b ∷ _) = b
first [] = false

native-correlated-traces : nativeTrace correlated repeat-word
  ≈Mℚ (Dmap (λ b → b ∷ b ∷ []) uniform-Bool >>=ᴹ return⊥)
native-correlated-traces ξ = trans (run-agreement correlated repeat-word false ξ)
  (>>=ᴹ-congʳ return⊥ (traceDist correlated repeat-word)
    (Dmap (λ b → b ∷ b ∷ []) uniform-Bool) (λ _ → refl) ξ)

native-correlated-consumer : experiment correlated repeat-word same-pair ≈Mℚ return⊥ true
native-correlated-consumer ξ = trans (experiment-agreement correlated repeat-word same-pair ξ)
  (trans (Dmap->>= (λ b → b ∷ b ∷ []) uniform-Bool (λ xs → return⊥ (same-pair xs)) ξ)
    (trans (>>=ᴹ-congˡ uniform-Bool (λ b → return⊥ (same-pair (b ∷ b ∷ [])))
      (λ _ → return⊥ true) (λ where false _ → refl ; true _ → refl) ξ)
      (>>=ᴹ-const uniform-Bool (return⊥ true) ξ)))

native-fair-marginal : lookupᴰℚ (entries (experiment correlated repeat-word first))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ ½
native-fair-marginal = refl

native-correlated-output-state : evalC
  (P.step (resource correlated) false false tt >>=ᶜ λ (q , _) → P.step (resource correlated) q true tt)
  ≈Mℚ (Dmap (λ b → b , just b) uniform-Bool >>=ᴹ return⊥)
native-correlated-output-state ξ = trans (native-bind-tick correlated false false
  (λ (q , _) → P.step (resource correlated) q true tt) ξ)
  (trans (Dmap->>= (λ b → (nothing {A = Bool}) , b) uniform-Bool
    (λ (o , q) → evalC (P.step (resource correlated) q true tt)) ξ)
    (trans (>>=ᴹ-congˡ uniform-Bool (λ q → evalC (P.step (resource correlated) q true tt))
      (λ b → return⊥ (b , just b)) output-law ξ)
      (sym (Dmap->>= (λ b → b , just b) uniform-Bool return⊥ ξ))))
  where
  output-law : ∀ b → evalC (P.step (resource correlated) b true tt) ≈Mℚ return⊥ (b , just b)
  output-law b ξ′ = trans (native-tick correlated b true ξ′)
    (trans (Dmap->>= swap (tick correlated true b) return⊥ ξ′)
      (trans (Dmap->>= (just b ,_) (return-ℚ b) (λ p → return⊥ (swap p)) ξ′)
        (>>=ᴹ-identityˡ b (λ q → return⊥ (q , just b)) ξ′)))

correlation-not-independent : ¬ (evalC
  (P.step (resource correlated) false false tt >>=ᶜ λ (q , _) → P.step (resource correlated) q true tt)
  ≈Mℚ (uniform-Bool >>=ᴹ λ b → uniform-Bool >>=ᴹ λ c → return⊥ (b , just c)))
correlation-not-independent e with e (maybeℚ (λ where
  (false , just true) → 1ℚ ; (true , just false) → 1ℚ ; _ → 0ℚ))
... | ()

native-send-first-computes : lookupᴰℚ (entries
  (experiment Source.network Source.send-first accept-receiver))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ 1ℚ
native-send-first-computes = refl

native-read-first-computes : lookupᴰℚ (entries
  (experiment Source.network Source.read-first accept-receiver))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ 0ℚ
native-read-first-computes = refl

native-disabled-computes : lookupᴰℚ (entries
  (experiment Source.pulse (true ∷ false ∷ true ∷ []) accept-pulse))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ 1ℚ
native-disabled-computes = refl

biased : Dist-ℚ Bool
biased = mk-Dist (((+ 1 / 3) , false) NE.∷ ((+ 2 / 3) , true) ∷ []) refl
  (toWitness {a? = 0ℚ ≤? (+ 1 / 3)} _ All.∷
   toWitness {a? = 0ℚ ≤? (+ 2 / 3)} _ All.∷ All.[])

biased-correlated : Automaton (Source.coinSignature empty)
biased-correlated = record correlated
  { kernel = λ where (inj₂ _) _ → biased ; (inj₁ _) b → return-ℚ b }

non-dyadic-native-consumer : lookupᴰℚ (entries (experiment biased-correlated repeat-word first))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ + 2 / 3
non-dyadic-native-consumer = refl
