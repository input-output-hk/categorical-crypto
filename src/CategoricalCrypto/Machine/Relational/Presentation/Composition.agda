{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Composition where

open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Trace
open import CategoricalCrypto.Machine.Relational.Presentation.Wiring
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C : Channel

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

  compose-presentation : {R : Initialized A B} {S : Initialized B C}
    → Presentation S → Presentation R → Presentation (S W.∘ R)
  compose-presentation {A} {B} {C} Q P = trace-presentation
    (reindex (M.∘σ {A} {B} {C}) rearrange left right (tensor-presentation P Q))
    where
    rearrange : (Channel.outType A ⊎ Channel.outType B) ⊎ (Channel.inType B ⊎ Channel.inType C)
              → (Channel.outType A ⊎ Channel.outType B) ⊎ (Channel.inType C ⊎ Channel.inType B)
    rearrange (inj₁ x) = inj₁ x
    rearrange (inj₂ (inj₁ b)) = inj₂ (inj₂ b)
    rearrange (inj₂ (inj₂ c)) = inj₂ (inj₁ c)
    left : ∀ o → app (M.∘σ {A} {B} {C} {Out}) (rearrange o) ≡ o
    left (inj₁ (inj₁ a)) = refl
    left (inj₁ (inj₂ b)) = refl
    left (inj₂ (inj₁ b)) = refl
    left (inj₂ (inj₂ c)) = refl
    right : ∀ o → rearrange (app (M.∘σ {A} {B} {C} {Out}) o) ≡ o
    right (inj₁ (inj₁ a)) = refl
    right (inj₁ (inj₂ b)) = refl
    right (inj₂ (inj₁ c)) = refl
    right (inj₂ (inj₂ b)) = refl

composition-shadow : {R : Initialized A B} {S : Initialized B C}
  (Q : Presentation S) (P : Presentation R) → shadow (compose-presentation Q P) ≈ᴿ (S W.∘ R)
composition-shadow Q P = presentation-correct (compose-presentation Q P)
