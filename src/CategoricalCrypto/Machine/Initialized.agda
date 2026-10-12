{-# OPTIONS --safe #-}

-- Finite initialized executions, separate from Machine.UC's all-state
-- isomorphism observation. Coins and divergence probabilities are absent.

module CategoricalCrypto.Machine.Initialized where

open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Iso

private variable A B : Channel

record InitializedMachine (A B : Channel) : Set₁ where
  constructor initialize
  field machine : Machine A B
        initial : Machine.State machine

open InitializedMachine

module _ (M : Machine A B) where
  open Channel (A ⊗ᵀ B)
  open Machine M

  data Steps : State → List (inType × Maybe outType) → State → Set where
    done : ∀ {s} → Steps s [] s
    next : ∀ {s i o s′ t s″} → stepRel s i o s′ → Steps s′ t s″
         → Steps s ((i , o) ∷ t) s″

Executes : (M : InitializedMachine A B)
         → List (Channel.inType (A ⊗ᵀ B) × Maybe (Channel.outType (A ⊗ᵀ B))) → Set
Executes M t = Σ[ s ∈ Machine.State (machine M) ] Steps (machine M) (initial M) t s

record _≅ⁱ_ (M N : InitializedMachine A B) : Set where
  constructor initializedIso
  field stateIso : machine M ≅ᴹ machine N
        initial-preserved : _≅ᴹ_.to stateIso (initial M) ≡ initial N

open _≅ⁱ_

≅ⁱ-refl : {M : InitializedMachine A B} → M ≅ⁱ M
≅ⁱ-refl = initializedIso ≅ᴹ-refl refl

≅ⁱ-sym : {M N : InitializedMachine A B} → M ≅ⁱ N → N ≅ⁱ M
≅ⁱ-sym {M = M} φ = initializedIso (≅ᴹ-sym (stateIso φ))
  (trans (cong (_≅ᴹ_.from (stateIso φ)) (sym (initial-preserved φ)))
         (_≅ᴹ_.from∘to (stateIso φ) (initial M)))

steps-to : {M N : Machine A B} (φ : M ≅ᴹ N) → ∀ {s t s′}
         → Steps M s t s′ → Steps N (_≅ᴹ_.to φ s) t (_≅ᴹ_.to φ s′)
steps-to φ done = done
steps-to φ (next p ps) = next (_≅ᴹ_.step-to φ p) (steps-to φ ps)

executes-to : {M N : InitializedMachine A B} → M ≅ⁱ N → ∀ {t}
            → Executes M t → Executes N t
executes-to {N = N} φ (s , ps) = _≅ᴹ_.to (stateIso φ) s ,
  subst (λ s₀ → Steps (machine N) s₀ _ _) (initial-preserved φ) (steps-to (stateIso φ) ps)

_≈ᵗ_ : InitializedMachine A B → InitializedMachine A B → Set
M ≈ᵗ N = ∀ t → Executes M t ⇔ Executes N t

≅ⁱ⇒≈ᵗ : {M N : InitializedMachine A B} → M ≅ⁱ N → M ≈ᵗ N
≅ⁱ⇒≈ᵗ φ _ = mk⇔ (executes-to φ) (executes-to (≅ⁱ-sym φ))
