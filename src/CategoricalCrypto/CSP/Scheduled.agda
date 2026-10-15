{-# OPTIONS --safe --without-K --guardedness #-}

-- Scheduling retains every label; an activation selects one whole global
-- transition, never a serialization of the participants in a Gather.
module CategoricalCrypto.CSP.Scheduled (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.Product.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload

module Schedule {A B : Interface} (N : Network A B) where
  open Execution N public
  module O = Observe N

  data Exact : Configuration → List Label → Configuration → Set where
    done : ∀ {p} → Exact p [] p
    next : ∀ {p l q ls r} → p ─[ l ]→ q → Exact q ls r → Exact p (l ∷ ls) r

  erase : List Label → List Visible
  erase [] = []
  erase (τ ∷ ls) = erase ls
  erase (visible e ∷ ls) = e ∷ erase ls

  forget-silent-labels : ∀ {p ls q} → Exact p ls q → O.Executes p (erase ls) q
  forget-silent-labels done = O.done
  forget-silent-labels (next {l = τ} step rest) = O.silent-step step (forget-silent-labels rest)
  forget-silent-labels (next {l = visible e} step rest) = O.visible-step step (forget-silent-labels rest)

  recover-silent-labels : ∀ {p xs q} → O.Executes p xs q
    → Σ (List Label) (λ ls → erase ls ≡ xs × Exact p ls q)
  recover-silent-labels O.done = [] , refl , done
  recover-silent-labels (O.silent-step step rest) =
    let ls , eq , exact = recover-silent-labels rest in τ ∷ ls , eq , next step exact
  recover-silent-labels (O.visible-step {e = e} step rest) =
    let ls , eq , exact = recover-silent-labels rest in visible e ∷ ls , cong (e ∷_) eq , next step exact

  ExactDivergence : Configuration → List Label → Set
  ExactDivergence p ls = Σ Configuration (λ q → Exact p ls q × Diverges q)

  divergence-observation : ∀ {p ls} → ExactDivergence p ls → O.Divergence p (erase ls)
  divergence-observation (q , path , divergent) = q , forget-silent-labels path , divergent

  recover-divergence-observation : ∀ {p xs} → O.Divergence p xs
    → Σ (List Label) (λ ls → erase ls ≡ xs × ExactDivergence p ls)
  recover-divergence-observation (q , path , divergent) =
    let ls , eq , exact = recover-silent-labels path in ls , eq , q , exact , divergent
