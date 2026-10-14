{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Network (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base hiding (reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
import CategoricalCrypto.CSP.Process as P

open Interface
open Port

-- Native Par⊤ components return unit. The independently reusable process core
-- retains arbitrary return types; no arbitrary-R network correspondence follows.
record Component : Set₁ where
  field
    boundary : Interface
    Branch : Set
    initial : P.Tree (Event boundary) Branch ⊤

open Component

record Boxes : Set₁ where
  constructor boxes
  field shape : Shape; label : ⟨ shape ⟩ → Component

open Boxes renaming (shape to box-shape)

Local : Boxes → Set
Local K = Σ ⟨ box-shape K ⟩ (λ k → ⟨ shape (boundary (label K k)) ⟩)

record Network (A B : Interface) : Set₁ where
  constructor mkNetwork
  no-eta-equality
  field
    components : Boxes
    private-shape : Shape
    private-sort : ⟨ private-shape ⟩ → Sort
    local-wire : Local components → ⟨ private-shape ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape B ⟩)
    wire-type : ∀ kp → sort (ports (boundary (label components (proj₁ kp))) (proj₂ kp))
                    ≡ [ private-sort , [ (λ i → sort (ports A i)) , (λ i → sort (ports B i)) ]′ ]′ (local-wire kp)
    aliases : List ((⟨ private-shape ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape B ⟩))
                  × (⟨ private-shape ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape B ⟩)))
    alias-type : ∀ {u v} → (u , v) ∈ aliases
                  → [ private-sort , [ (λ i → sort (ports A i)) , (λ i → sort (ports B i)) ]′ ]′ u
                  ≡ [ private-sort , [ (λ i → sort (ports A i)) , (λ i → sort (ports B i)) ]′ ]′ v

-- A closure proof cannot manufacture a transition: operational rules separately
-- require inhabited participating component moves, including on private classes.
module Wiring {A B : Interface} (N : Network A B) where
  open Network N

  Name : Set
  Name = ⟨ private-shape ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape B ⟩)

  name-sort : Name → Sort
  name-sort = [ private-sort , [ (λ i → sort (ports A i)) , (λ i → sort (ports B i)) ]′ ]′

  data Connected : Name → Name → Set where
    same : ∀ {u} → Connected u u
    alias : ∀ {u v} → (u , v) ∈ aliases → Connected u v
    reverse : ∀ {u v} → Connected u v → Connected v u
    join : ∀ {u v w} → Connected u v → Connected v w → Connected u w

  connected-type : ∀ {u v} → Connected u v → name-sort u ≡ name-sort v
  connected-type same = refl
  connected-type (alias a) = alias-type a
  connected-type (reverse p) = sym (connected-type p)
  connected-type (join p q) = trans (connected-type p) (connected-type q)

  State : Set
  State = (k : ⟨ box-shape components ⟩) → P.Tree (Event (boundary (label components k)))
                    (Branch (label components k)) ⊤

  initial-state : State
  initial-state k = initial (label components k)
