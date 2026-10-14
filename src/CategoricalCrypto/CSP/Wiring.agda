{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Wiring (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload

map-connected : ∀ {A B C D} {F : Network A B} {G : Network C D}
  (f : Wiring.Name F → Wiring.Name G)
  → (∀ {u v} → (u , v) ∈ Network.aliases F → Wiring.Connected G (f u) (f v))
  → ∀ {u v} → Wiring.Connected F u v → Wiring.Connected G (f u) (f v)
map-connected f edge Wiring.same = Wiring.same
map-connected f edge (Wiring.alias a) = edge a
map-connected f edge (Wiring.reverse p) = Wiring.reverse (map-connected f edge p)
map-connected f edge (Wiring.join p q) = Wiring.join (map-connected f edge p) (map-connected f edge q)

module Plug {A B C : Interface} (F : Network A B) (G : Network B C) where
  module C = Compose F G
  module W = Wiring (G ∘ F)

  left-connected : ∀ {u v} → Wiring.Connected F u v → W.Connected (C.left u) (C.left v)
  left-connected = map-connected C.left (λ a → W.alias (∈-++⁺ˡ (∈-map⁺ (map-edge C.left) a)))

  right-connected : ∀ {u v} → Wiring.Connected G u v → W.Connected (C.right u) (C.right v)
  right-connected = map-connected C.right (λ a → W.alias
    (∈-++⁺ʳ (map (map-edge C.left) (Network.aliases F)) (∈-map⁺ (map-edge C.right) a)))

module Disjoint {A B C D : Interface} (F : Network A B) (G : Network C D) where
  module T = Tensor F G
  module W = Wiring (F ⊗₁ G)

  left-connected : ∀ {u v} → Wiring.Connected F u v → W.Connected (T.left u) (T.left v)
  left-connected = map-connected T.left (λ a → W.alias (∈-++⁺ˡ (∈-map⁺ (map-edge T.left) a)))

  right-connected : ∀ {u v} → Wiring.Connected G u v → W.Connected (T.right u) (T.right v)
  right-connected = map-connected T.right (λ a → W.alias
    (∈-++⁺ʳ (map (map-edge T.left) (Network.aliases F)) (∈-map⁺ (map-edge T.right) a)))

identity-alias : ∀ {A} i → Wiring.Connected (id {A}) (inj₂ (inj₁ i)) (inj₂ (inj₂ i))
identity-alias {A} i = Wiring.alias (∈-map⁺ (Identity.edge A) (enumerate-complete (Interface.shape A) i))
