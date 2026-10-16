{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Observation where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Category
open import CategoricalCrypto.UC.Core

-- These are channel(unitᴵ) and channel(Ωᴵ), without a dependency on a
-- probabilistic implementation or its observation function.
J Ω : Channel
J = ⊥ ⇿ ⊥
Ω = Bool ⇿ ⊤

opaque
  unfolding _⊗₀_

  tick : Channel.inType (J M.⊗ᵀ Ω)
  tick = inj₂ tt

  verdict : Bool → Channel.outType (J M.⊗ᵀ Ω)
  verdict = inj₂

-- A native step contains the finite internal interaction introduced by wiring.
-- A refusal (nothing), or absence of a finite reply, witnesses neither Boolean.
eval : Initialized J Ω → Bool → Set
eval P b = ∃ λ s → initial P s × ∃ λ t → M.Machine.stepRel (machine P) s tick (just (verdict b)) t

eval-to : {P Q : Initialized J Ω} → P ≈ᴿ Q → ∀ {b} → eval P b → eval Q b
eval-to φ (s , p , s′ , step) =
  let t , q , st = initial-to φ p
      t′ , step′ , st′ = step-to φ st step
  in t , q , t′ , step′

eval-resp : {P Q : Initialized J Ω} → P ≈ᴿ Q → ∀ b → eval P b ⇔ eval Q b
eval-resp φ b = mk⇔ (eval-to φ) (eval-to (≈ᴿ-sym φ))

Verdicts : Setoid (suc 0ℓ) 0ℓ
Verdicts = record
  { Carrier = Bool → Set
  ; _≈_ = λ P Q → ∀ b → P b ⇔ Q b
  ; isEquivalence = record
    { refl = λ b → mk⇔ (λ p → p) (λ p → p)
    ; sym = λ eq b → mk⇔ (Equivalence.from (eq b)) (Equivalence.to (eq b))
    ; trans = λ eq eq′ b → mk⇔
        (λ p → Equivalence.to (eq′ b) (Equivalence.to (eq b) p))
        (λ p → Equivalence.from (eq b) (Equivalence.from (eq′ b) p)) }
  }

evaluation : Evaluation 𝓡 (suc 0ℓ) 0ℓ
evaluation = record
  { J = J ; Ω = Ω ; S = Verdicts
  ; eval = record { to = eval ; cong = eval-resp }
  }
