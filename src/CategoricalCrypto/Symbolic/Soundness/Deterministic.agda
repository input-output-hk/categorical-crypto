{-# OPTIONS --safe --without-K #-}

-- Exact labeled traces of total deterministic Mealy transitions determine a
-- strong bisimulation. This is not the missing applied-π observational-equivalence
-- bridge: the symbolic setup compares verdicts of closed DY contexts, not these
-- raw labeled traces (docs/uc-setup-symbolic.md §4.3).

module CategoricalCrypto.Symbolic.Soundness.Deterministic where

open import Data.List.Base
open import Data.List.Properties
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

module _ {i o s t : Level} {I : Set i} {O : Set o} {S : Set s} {T : Set t}
         (stepS : S → I → S × O) (stepT : T → I → T × O) where

  traces : {u : Level} {U : Set u} → (U → I → U × O) → U → List I → List O
  traces step q [] = []
  traces step q (x ∷ xs) = proj₂ (step q x) ∷ traces step (proj₁ (step q x)) xs

  TraceEqual : S → T → Set (i ⊔ o)
  TraceEqual q r = (xs : List I) → traces stepS q xs ≡ traces stepT r xs

  record Bisimulation (q : S) (r : T) : Set (s ⊔ t ⊔ suc (i ⊔ o)) where
    field
      Related : S → T → Set (i ⊔ o)
      initial : Related q r
      output : ∀ {q r} → Related q r → (x : I) → proj₂ (stepS q x) ≡ proj₂ (stepT r x)
      next : ∀ {q r} → Related q r → (x : I) → Related (proj₁ (stepS q x)) (proj₁ (stepT r x))

  trace⇒bisim : ∀ {q r} → TraceEqual q r → Bisimulation q r
  trace⇒bisim h = record
    { Related = TraceEqual ; initial = h
    ; output = λ e x → ∷-injectiveˡ (e (x ∷ []))
    ; next = λ e x xs → ∷-injectiveʳ (e (x ∷ xs)) }
