{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryOperational (X B : Set) where

open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.CSP.BinaryNetwork as Network
import CategoricalCrypto.CSP.BinaryScheduled as Binary
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Relational as R
import CategoricalCrypto.Machine.Relational.Wiring as W

module N = Network X B
module S = Binary (⊤ × X) B

module Connection (p₀ q₀ : N.P.Tree) where
  open N.Native p₀ q₀ public

  data Step : M.MachineType S.scheduler S.result E.Configuration where
    left : ∀ {q p′} → N.P._─[_]→_ (q (inj₁ tt)) N.P.τ p′
      → Step (E.running q) (S.input (inj₁ S.leftτ)) (S.output (just (inj₁ S.τ)))
          (E.running (E.update (inj₁ tt) p′ q))
    right : ∀ {q p′} → N.P._─[_]→_ (q (inj₂ tt)) N.P.τ p′
      → Step (E.running q) (S.input (inj₁ S.rightτ)) (S.output (just (inj₂ S.τ)))
          (E.running (E.update (inj₂ tt) p′ q))
    exchange : ∀ {q q′ x} → E.Gather (inj₁ tt) x q q′
      → Step (E.running q) (S.input (inj₁ S.sync)) (S.output (just (inj₂ S.τ))) (E.running q′)
    finish : ∀ {q} → E.AllRet q
      → Step (E.running q) (S.input (inj₁ S.finish)) (S.output (just (inj₂ S.√))) E.completed

  scheduled : R.Initialized S.scheduler S.result
  scheduled = R.singleton (M.MkMachine Step) E.initial-configuration

  interpreted : R.Initialized S.scheduler S.result
  interpreted = R.singleton S.specification (S.live p₀ , S.live q₀)

  compiled : R.Initialized S.scheduler S.result
  compiled = R.singleton S.compiled (S.live p₀ , S.live q₀)

  data Related : E.Configuration → S.LocalState × S.LocalState → Set where
    running : ∀ {q p r} → q (inj₁ tt) ≡ p → q (inj₂ tt) ≡ r
      → Related (E.running q) (S.live p , S.live r)
    completed : Related E.completed (S.completed , S.completed)

  source-to-joint : ∀ {p q i o p′} → Related p q → Step p i o p′
    → Σ (S.LocalState × S.LocalState) (λ q′ → S.Joint q i o q′ × Related p′ q′)
  source-to-joint (running refl refl) (left move) = _ , S.Joint.left move , running refl refl
  source-to-joint (running refl refl) (right move) = _ , S.Joint.right move , running refl refl
  source-to-joint (running refl refl) (exchange g) = _ , S.handshake (gather-left g) (gather-right g) , running refl refl
  source-to-joint (running refl refl) (finish ready) = _ , S.Joint.finish (ready (inj₁ tt)) (ready (inj₂ tt)) , completed

  joint-to-source : ∀ {p q i o q′} → Related p q → S.Joint q i o q′
    → Σ E.Configuration (λ p′ → Step p i o p′ × Related p′ q′)
  joint-to-source (running refl refl) (S.Joint.left move) = _ , left move , running refl refl
  joint-to-source (running refl refl) (S.Joint.right move) = _ , right move , running refl refl
  joint-to-source (running refl refl) (S.handshake {x = tt , x} sp sq) = _ ,
    exchange (gather-state {q′ = pair _ _} sp sq) , running refl refl
  joint-to-source (running refl refl) (S.Joint.finish sp sq) = _ ,
    finish (λ { (inj₁ tt) → sp ; (inj₂ tt) → sq }) , completed

  scheduled-correct : scheduled R.≈ᴿ interpreted
  scheduled-correct = record
    { Related = Related
    ; initial-to = λ { refl → _ , refl , running refl refl }
    ; initial-from = λ { refl → _ , refl , running refl refl }
    ; step-to = source-to-joint ; step-from = joint-to-source }

  wiring-correct : interpreted R.≈ᴿ compiled
  wiring-correct = record
    { Related = _≡_
    ; initial-to = λ { refl → _ , refl , refl }
    ; initial-from = λ { refl → _ , refl , refl }
    ; step-to = λ { refl step → _ , S.joint-to-compiled step , refl }
    ; step-from = λ { refl step → _ , S.compiled-to-joint step , refl } }

  native-composition-correct : scheduled R.≈ᴿ compiled
  native-composition-correct = R.≈ᴿ-trans scheduled-correct wiring-correct

  components : R.Initialized S.scheduler S.result
  components = (R.singleton S.receiver (S.live q₀)) W.∘ (R.singleton S.sender (S.live p₀))

  component-initialization : compiled R.≈ᴿ components
  component-initialization = record
    { Related = _≡_
    ; initial-to = λ { refl → _ , (refl , refl) , refl }
    ; initial-from = λ { (refl , refl) → _ , refl , refl }
    ; step-to = λ { refl step → _ , step , refl }
    ; step-from = λ { refl step → _ , step , refl } }

  native-components-correct : scheduled R.≈ᴿ components
  native-components-correct = R.≈ᴿ-trans native-composition-correct component-initialization

  erase-step : ∀ {p i o q} → Step p i o q → Σ E.Label (λ l → E._─[_]→_ p l q)
  erase-step (left move) = E.τ , E.internal move
  erase-step (right move) = E.τ , E.internal move
  erase-step (exchange g) = E.τ , E.hidden _ g (λ { (inj₁ ()) ; (inj₂ ()) }) (handshake g)
  erase-step (finish ready) = E.visible E.√ , E.finish (inj₁ tt) ready

  recover-step : ∀ {p l q} → E._─[_]→_ p l q → ∃ λ i → ∃ λ o → Step p i o q
  recover-step (E.internal {k = inj₁ tt} move) = _ , _ , left move
  recover-step (E.internal {k = inj₂ tt} move) = _ , _ , right move
  recover-step (E.hidden {n = inj₁ tt} x g confined supported) = _ , _ , exchange g
  recover-step (E.hidden {n = inj₂ (inj₁ ())} x g confined supported)
  recover-step (E.hidden {n = inj₂ (inj₂ ())} x g confined supported)
  recover-step (E.exterior {e = inj₁ ()} x g compatible)
  recover-step (E.exterior {e = inj₂ ()} x g compatible)
  recover-step (E.finish box ready) = _ , _ , finish ready
