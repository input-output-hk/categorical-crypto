{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational where

open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Initialized using (Steps; done; next)

private variable A B : Channel

record Initialized (A B : Channel) : Set₁ where
  constructor initialize
  field machine : M.Machine A B
        initial : M.Machine.State machine → Set

open Initialized public

singleton : (M : M.Machine A B) → M.Machine.State M → Initialized A B
singleton M s = initialize M (s ≡_)

record _≈ᴿ_ (P Q : Initialized A B) : Set₁ where
  field
    Related : M.Machine.State (machine P) → M.Machine.State (machine Q) → Set
    initial-to : ∀ {s} → initial P s → ∃ λ t → initial Q t × Related s t
    initial-from : ∀ {t} → initial Q t → ∃ λ s → initial P s × Related s t
    step-to : ∀ {s t i o s′} → Related s t → M.Machine.stepRel (machine P) s i o s′
            → ∃ λ t′ → M.Machine.stepRel (machine Q) t i o t′ × Related s′ t′
    step-from : ∀ {s t i o t′} → Related s t → M.Machine.stepRel (machine Q) t i o t′
              → ∃ λ s′ → M.Machine.stepRel (machine P) s i o s′ × Related s′ t′

open _≈ᴿ_ public

≈ᴿ-refl : {P : Initialized A B} → P ≈ᴿ P
≈ᴿ-refl = record
  { Related = _≡_
  ; initial-to = λ p → _ , p , refl
  ; initial-from = λ p → _ , p , refl
  ; step-to = λ { refl p → _ , p , refl }
  ; step-from = λ { refl p → _ , p , refl }
  }

≈ᴿ-sym : {P Q : Initialized A B} → P ≈ᴿ Q → Q ≈ᴿ P
≈ᴿ-sym φ = record
  { Related = λ t s → Related φ s t
  ; initial-to = initial-from φ
  ; initial-from = initial-to φ
  ; step-to = step-from φ
  ; step-from = step-to φ
  }

≈ᴿ-trans : {P Q R : Initialized A B} → P ≈ᴿ Q → Q ≈ᴿ R → P ≈ᴿ R
≈ᴿ-trans {Q = Q} φ ψ = record
  { Related = λ s u → ∃ λ t → Related φ s t × Related ψ t u
  ; initial-to = λ p →
      let t , q , st = initial-to φ p
          u , r , tu = initial-to ψ q
      in u , r , t , st , tu
  ; initial-from = λ r →
      let t , q , tu = initial-from ψ r
          s , p , st = initial-from φ q
      in s , p , t , st , tu
  ; step-to = λ { (t , st , tu) p →
      let t′ , q , st′ = step-to φ st p
          u′ , r , tu′ = step-to ψ tu q
      in u′ , r , t′ , st′ , tu′ }
  ; step-from = λ { (t , st , tu) r →
      let t′ , q , tu′ = step-from ψ tu r
          s′ , p , st′ = step-from φ st q
      in s′ , p , t′ , st′ , tu′ }
  }

steps-to : {P Q : Initialized A B} (φ : P ≈ᴿ Q) → ∀ {s t l s′}
         → Related φ s t → Steps (machine P) s l s′
         → ∃ λ t′ → Steps (machine Q) t l t′ × Related φ s′ t′
steps-to φ st done = _ , done , st
steps-to φ st (next p ps) =
  let t′ , q , st′ = step-to φ st p
      t″ , qs , st″ = steps-to φ st′ ps
  in t″ , next q qs , st″

steps-from : {P Q : Initialized A B} (φ : P ≈ᴿ Q) → ∀ {s t l t′}
           → Related φ s t → Steps (machine Q) t l t′
           → ∃ λ s′ → Steps (machine P) s l s′ × Related φ s′ t′
steps-from φ = steps-to (≈ᴿ-sym φ)

Executes : (P : Initialized A B)
         → List (Channel.inType (A M.⊗ᵀ B) × Maybe (Channel.outType (A M.⊗ᵀ B))) → Set
Executes P l = ∃ λ s → initial P s × ∃ λ t → Steps (machine P) s l t

executes-to : {P Q : Initialized A B} → P ≈ᴿ Q → ∀ {l} → Executes P l → Executes Q l
executes-to φ (s , p , s′ , ps) =
  let t , q , st = initial-to φ p
      t′ , qs , st′ = steps-to φ st ps
  in t , q , t′ , qs

executes-from : {P Q : Initialized A B} → P ≈ᴿ Q → ∀ {l} → Executes Q l → Executes P l
executes-from φ = executes-to (≈ᴿ-sym φ)

execution-invariant : {P Q : Initialized A B} → P ≈ᴿ Q → ∀ l → Executes P l ⇔ Executes Q l
execution-invariant φ l = mk⇔ (executes-to φ) (executes-from φ)
