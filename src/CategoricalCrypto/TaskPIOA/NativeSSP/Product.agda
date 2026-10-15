{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.Product where

open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Coins
open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; sample)
open import CategoricalCrypto.TaskPIOA.Core using
  (Signature; Wiring; empty; productSignature; _⊠_; Task; Local; leftAction; rightAction; find; left; right)
import CategoricalCrypto.TaskPIOA.Product as Source
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.Simulation
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

module _ {A B J} (w : Wiring A B J) (M : Machine A) (N : Machine B) where
  private S = productSignature A B J

  selection : State M × State N → Task S → Maybe (Local S)
  selection (q , r) (inj₁ t) = Maybe.map (leftAction {A} {B}) (select M q t)
  selection (q , r) (inj₂ t) = Maybe.map (rightAction {A} {B}) (select N r t)

  advance : Local S → State M × State N → Coins (State M × State N)
  advance (inj₁ (inj₁ o)) (q , r) = pairCoins (transition M (inj₁ o) q)
    (receive N (find (right w) (inj₂ o)) r)
  advance (inj₁ (inj₂ o)) (q , r) = pairCoins
    (receive M (find (left w) (inj₂ o)) q) (transition N (inj₁ o) r)
  advance (inj₂ (inj₁ h)) (q , r) = pairCoins (transition M (inj₂ h) q) (done r)
  advance (inj₂ (inj₂ h)) (q , r) = pairCoins (done q) (transition N (inj₂ h) r)

  connect : Machine S
  connect = record
    { memory = memory M ⊠ memory N ; start = start M , start N
    ; deliver = λ i (q , r) → pairCoins (receive M (find (left w) (inj₁ i)) q)
      (receive N (find (right w) (inj₁ i)) r)
    ; select = selection
    ; owned = λ where
        (q , r) (inj₁ t) a p → Source.product-owns w (sampleMachine M) (sampleMachine N) (q , r) (inj₁ t) a p
        (q , r) (inj₂ t) a p → Source.product-owns w (sampleMachine M) (sampleMachine N) (q , r) (inj₂ t) a p
    ; transition = advance }

receive-sample : ∀ {S} (M : Machine S) i q
  → sample (receive M i q) ≈Mℚ Source.receive (sampleMachine M) i q
receive-sample M nothing q P = refl
receive-sample M (just i) q P = refl

module _ {A B J} (w : Wiring A B J) (M : Machine A) (N : Machine B) where
  private
    L = sampleMachine (connect w M N)
    R = Source.product w (sampleMachine M) (sampleMachine N)

    pair-law : (κ : Coins (State M)) (λκ : Coins (State N))
      (μ : Dist-ℚ (State M)) (ν : Dist-ℚ (State N))
      → sample κ ≈Mℚ μ → sample λκ ≈Mℚ ν
      → sample (pairCoins κ λκ) ≈Mℚ independent μ ν
    pair-law κ λκ μ ν p r P = trans (sample-pair κ λκ P)
      (independent-cong (sample κ) μ (sample λκ) ν p r P)

    input-law : ∀ i q → CategoricalCrypto.TaskPIOA.Core.input L i q
      ≈Mℚ CategoricalCrypto.TaskPIOA.Core.input R i q
    input-law i (q , r) = pair-law
      (receive M (find (left w) (inj₁ i)) q) (receive N (find (right w) (inj₁ i)) r)
      (Source.receive (sampleMachine M) (find (left w) (inj₁ i)) q)
      (Source.receive (sampleMachine N) (find (right w) (inj₁ i)) r)
      (receive-sample M (find (left w) (inj₁ i)) q)
      (receive-sample N (find (right w) (inj₁ i)) r)

    local-law : ∀ a q → CategoricalCrypto.TaskPIOA.Core.kernel L a q
      ≈Mℚ CategoricalCrypto.TaskPIOA.Core.kernel R a q
    local-law (inj₁ (inj₁ o)) (q , r) = pair-law
      (transition M (inj₁ o) q) (receive N (find (right w) (inj₂ o)) r)
      (sample (transition M (inj₁ o) q))
      (Source.receive (sampleMachine N) (find (right w) (inj₂ o)) r)
      (λ _ → refl) (receive-sample N (find (right w) (inj₂ o)) r)
    local-law (inj₁ (inj₂ o)) (q , r) = pair-law
      (receive M (find (left w) (inj₂ o)) q) (transition N (inj₁ o) r)
      (Source.receive (sampleMachine M) (find (left w) (inj₂ o)) q)
      (sample (transition N (inj₁ o) r))
      (receive-sample M (find (left w) (inj₂ o)) q) (λ _ → refl)
    local-law (inj₂ (inj₁ h)) (q , r) = sample-pair (transition M (inj₂ h) q) (done r)
    local-law (inj₂ (inj₂ h)) (q , r) = sample-pair (done q) (transition N (inj₂ h) r)

  connect-sample : Simulation L R
  connect-sample = record
    { stateMap = id ; starts = refl
    ; choices = λ where (q , r) (inj₁ t) → refl ; (q , r) (inj₂ t) → refl
    ; inputs-match = λ i q P → trans (Dmap-id (CategoricalCrypto.TaskPIOA.Core.input L i q) P) (input-law i q P)
    ; local-match = λ a q P → trans (Dmap-id (CategoricalCrypto.TaskPIOA.Core.kernel L a q) P) (local-law a q P) }

  sample-connect : Simulation R L
  sample-connect = record
    { stateMap = id ; starts = refl
    ; choices = λ where (q , r) (inj₁ t) → refl ; (q , r) (inj₂ t) → refl
    ; inputs-match = λ i q P → trans (Dmap-id (CategoricalCrypto.TaskPIOA.Core.input R i q) P) (sym (input-law i q P))
    ; local-match = λ a q P → trans (Dmap-id (CategoricalCrypto.TaskPIOA.Core.kernel R a q) P) (sym (local-law a q P)) }

record Environment (S : Signature) : Set where
  field signature : Signature
        machine : Machine signature
        wiring : Wiring S signature empty
open Environment public
