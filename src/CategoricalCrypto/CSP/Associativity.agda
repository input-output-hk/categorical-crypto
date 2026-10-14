{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Associativity (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Wiring Sort Payload

module Flatten {A B C D : Interface} (F : Network A B) (G : Network B C) (H : Network C D) where
  module SI = Compose F G
  module SO = Compose (G ∘ F) H
  module TI = Compose G H
  module TO = Compose F (H ∘ G)
  module S = Wiring (H ∘ (G ∘ F))
  module T = Wiring ((H ∘ G) ∘ F)
  module SIP = Plug F G
  module SOP = Plug (G ∘ F) H
  module TIP = Plug G H
  module TOP = Plug F (H ∘ G)

  forward-name : S.Name → T.Name
  forward-name (inj₁ (inj₁ (inj₁ (inj₁ (inj₁ p))))) = inj₁ (inj₁ (inj₁ p))
  forward-name (inj₁ (inj₁ (inj₁ (inj₁ (inj₂ b))))) = inj₁ (inj₁ (inj₂ b))
  forward-name (inj₁ (inj₁ (inj₁ (inj₂ p)))) = inj₁ (inj₂ (inj₁ (inj₁ p)))
  forward-name (inj₁ (inj₁ (inj₂ c))) = inj₁ (inj₂ (inj₁ (inj₂ c)))
  forward-name (inj₁ (inj₂ p)) = inj₁ (inj₂ (inj₂ p))
  forward-name (inj₂ e) = inj₂ e

  backward-name : T.Name → S.Name
  backward-name (inj₁ (inj₁ (inj₁ p))) = inj₁ (inj₁ (inj₁ (inj₁ (inj₁ p))))
  backward-name (inj₁ (inj₁ (inj₂ b))) = inj₁ (inj₁ (inj₁ (inj₁ (inj₂ b))))
  backward-name (inj₁ (inj₂ (inj₁ (inj₁ p)))) = inj₁ (inj₁ (inj₁ (inj₂ p)))
  backward-name (inj₁ (inj₂ (inj₁ (inj₂ c)))) = inj₁ (inj₁ (inj₂ c))
  backward-name (inj₁ (inj₂ (inj₂ p))) = inj₁ (inj₂ p)
  backward-name (inj₂ e) = inj₂ e

  forward-type : ∀ n → S.name-sort n ≡ T.name-sort (forward-name n)
  forward-type (inj₁ (inj₁ (inj₁ (inj₁ (inj₁ p))))) = refl
  forward-type (inj₁ (inj₁ (inj₁ (inj₁ (inj₂ b))))) = refl
  forward-type (inj₁ (inj₁ (inj₁ (inj₂ p)))) = refl
  forward-type (inj₁ (inj₁ (inj₂ c))) = refl
  forward-type (inj₁ (inj₂ p)) = refl
  forward-type (inj₂ (inj₁ a)) = refl
  forward-type (inj₂ (inj₂ d)) = refl

  backward-type : ∀ n → T.name-sort n ≡ S.name-sort (backward-name n)
  backward-type (inj₁ (inj₁ (inj₁ p))) = refl
  backward-type (inj₁ (inj₁ (inj₂ b))) = refl
  backward-type (inj₁ (inj₂ (inj₁ (inj₁ p)))) = refl
  backward-type (inj₁ (inj₂ (inj₁ (inj₂ c)))) = refl
  backward-type (inj₁ (inj₂ (inj₂ p))) = refl
  backward-type (inj₂ (inj₁ a)) = refl
  backward-type (inj₂ (inj₂ d)) = refl

  forward-F : ∀ n → forward-name (SO.left (SI.left n)) ≡ TO.left n
  forward-F (inj₁ _) = refl
  forward-F (inj₂ (inj₁ _)) = refl
  forward-F (inj₂ (inj₂ _)) = refl

  forward-G : ∀ n → forward-name (SO.left (SI.right n)) ≡ TO.right (TI.left n)
  forward-G (inj₁ _) = refl
  forward-G (inj₂ (inj₁ _)) = refl
  forward-G (inj₂ (inj₂ _)) = refl

  forward-H : ∀ n → forward-name (SO.right n) ≡ TO.right (TI.right n)
  forward-H (inj₁ _) = refl
  forward-H (inj₂ (inj₁ _)) = refl
  forward-H (inj₂ (inj₂ _)) = refl

  backward-F : ∀ n → backward-name (TO.left n) ≡ SO.left (SI.left n)
  backward-F (inj₁ _) = refl
  backward-F (inj₂ (inj₁ _)) = refl
  backward-F (inj₂ (inj₂ _)) = refl

  backward-G : ∀ n → backward-name (TO.right (TI.left n)) ≡ SO.left (SI.right n)
  backward-G (inj₁ _) = refl
  backward-G (inj₂ (inj₁ _)) = refl
  backward-G (inj₂ (inj₂ _)) = refl

  backward-H : ∀ n → backward-name (TO.right (TI.right n)) ≡ SO.right n
  backward-H (inj₁ _) = refl
  backward-H (inj₂ (inj₁ _)) = refl
  backward-H (inj₂ (inj₂ _)) = refl

  forward-F-edge : ∀ {u v} → (u , v) ∈ Network.aliases F
    → T.Connected (forward-name (SO.left (SI.left u))) (forward-name (SO.left (SI.left v)))
  forward-F-edge {u} {v} member = T.join (connection-equality (forward-F u))
    (T.join (TOP.left-connected (Wiring.alias member)) (T.reverse (connection-equality (forward-F v))))

  forward-G-edge : ∀ {u v} → (u , v) ∈ Network.aliases G
    → T.Connected (forward-name (SO.left (SI.right u))) (forward-name (SO.left (SI.right v)))
  forward-G-edge {u} {v} member = T.join (connection-equality (forward-G u))
    (T.join (TOP.right-connected (TIP.left-connected (Wiring.alias member))) (T.reverse (connection-equality (forward-G v))))

  forward-H-edge : ∀ {u v} → (u , v) ∈ Network.aliases H
    → T.Connected (forward-name (SO.right u)) (forward-name (SO.right v))
  forward-H-edge {u} {v} member = T.join (connection-equality (forward-H u))
    (T.join (TOP.right-connected (TIP.right-connected (Wiring.alias member))) (T.reverse (connection-equality (forward-H v))))

  forward-inner : ∀ {u v} → (u , v) ∈ SI.aliases
    → T.Connected (forward-name (SO.left u)) (forward-name (SO.left v))
  forward-inner member with ∈-++⁻ (map (map-edge SI.left) (Network.aliases F)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge SI.left) mem
  ... | (u , v) , edge , refl = forward-F-edge edge
  forward-inner member | inj₂ mem with ∈-map⁻ (map-edge SI.right) mem
  ... | (u , v) , edge , refl = forward-G-edge edge

  forward-left : ∀ {u v} → (u , v) ∈ map (map-edge SO.left) SI.aliases
    → T.Connected (forward-name u) (forward-name v)
  forward-left member with ∈-map⁻ (map-edge SO.left) member
  ... | (u , v) , edge , refl = forward-inner edge

  forward-right : ∀ {u v} → (u , v) ∈ map (map-edge SO.right) (Network.aliases H)
    → T.Connected (forward-name u) (forward-name v)
  forward-right member with ∈-map⁻ (map-edge SO.right) member
  ... | (u , v) , edge , refl = forward-H-edge edge

  forward-connected : ∀ {u v} → S.Connected u v → T.Connected (forward-name u) (forward-name v)
  forward-connected = map-connected forward-name (λ member → [ forward-left , forward-right ]′
    (∈-++⁻ (map (map-edge SO.left) SI.aliases) member))

  backward-F-edge : ∀ {u v} → (u , v) ∈ Network.aliases F
    → S.Connected (backward-name (TO.left u)) (backward-name (TO.left v))
  backward-F-edge {u} {v} member = S.join (connection-equality (backward-F u))
    (S.join (SOP.left-connected (SIP.left-connected (Wiring.alias member))) (S.reverse (connection-equality (backward-F v))))

  backward-G-edge : ∀ {u v} → (u , v) ∈ Network.aliases G
    → S.Connected (backward-name (TO.right (TI.left u))) (backward-name (TO.right (TI.left v)))
  backward-G-edge {u} {v} member = S.join (connection-equality (backward-G u))
    (S.join (SOP.left-connected (SIP.right-connected (Wiring.alias member))) (S.reverse (connection-equality (backward-G v))))

  backward-H-edge : ∀ {u v} → (u , v) ∈ Network.aliases H
    → S.Connected (backward-name (TO.right (TI.right u))) (backward-name (TO.right (TI.right v)))
  backward-H-edge {u} {v} member = S.join (connection-equality (backward-H u))
    (S.join (SOP.right-connected (Wiring.alias member)) (S.reverse (connection-equality (backward-H v))))

  backward-inner : ∀ {u v} → (u , v) ∈ TI.aliases
    → S.Connected (backward-name (TO.right u)) (backward-name (TO.right v))
  backward-inner member with ∈-++⁻ (map (map-edge TI.left) (Network.aliases G)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge TI.left) mem
  ... | (u , v) , edge , refl = backward-G-edge edge
  backward-inner member | inj₂ mem with ∈-map⁻ (map-edge TI.right) mem
  ... | (u , v) , edge , refl = backward-H-edge edge

  backward-left : ∀ {u v} → (u , v) ∈ map (map-edge TO.left) (Network.aliases F)
    → S.Connected (backward-name u) (backward-name v)
  backward-left member with ∈-map⁻ (map-edge TO.left) member
  ... | (u , v) , edge , refl = backward-F-edge edge

  backward-right : ∀ {u v} → (u , v) ∈ map (map-edge TO.right) TI.aliases
    → S.Connected (backward-name u) (backward-name v)
  backward-right member with ∈-map⁻ (map-edge TO.right) member
  ... | (u , v) , edge , refl = backward-inner edge

  backward-connected : ∀ {u v} → T.Connected u v → S.Connected (backward-name u) (backward-name v)
  backward-connected = map-connected backward-name (λ member → [ backward-left , backward-right ]′
    (∈-++⁻ (map (map-edge TO.left) (Network.aliases F)) member))

  names-left : ∀ n → backward-name (forward-name n) ≡ n
  names-left (inj₁ (inj₁ (inj₁ (inj₁ (inj₁ _))))) = refl
  names-left (inj₁ (inj₁ (inj₁ (inj₁ (inj₂ _))))) = refl
  names-left (inj₁ (inj₁ (inj₁ (inj₂ _)))) = refl
  names-left (inj₁ (inj₁ (inj₂ _))) = refl
  names-left (inj₁ (inj₂ _)) = refl
  names-left (inj₂ _) = refl

  names-right : ∀ n → forward-name (backward-name n) ≡ n
  names-right (inj₁ (inj₁ (inj₁ _))) = refl
  names-right (inj₁ (inj₁ (inj₂ _))) = refl
  names-right (inj₁ (inj₂ (inj₁ (inj₁ _)))) = refl
  names-right (inj₁ (inj₂ (inj₁ (inj₂ _)))) = refl
  names-right (inj₁ (inj₂ (inj₂ _))) = refl
  names-right (inj₂ _) = refl

  forward : Embedding (H ∘ (G ∘ F)) ((H ∘ G) ∘ F)
  forward = record
    { box-map = λ { (inj₁ (inj₁ k)) → inj₁ k ; (inj₁ (inj₂ k)) → inj₂ (inj₁ k) ; (inj₂ k) → inj₂ (inj₂ k) }
    ; box-label = λ { (inj₁ (inj₁ k)) → refl ; (inj₁ (inj₂ k)) → refl ; (inj₂ k) → refl }
    ; name-map = forward-name ; name-type = forward-type ; connected = forward-connected
    ; external = λ _ → T.same
    ; local = λ { (inj₁ (inj₁ k)) p → connection-equality (forward-F (Network.local-wire F (k , p)))
                ; (inj₁ (inj₂ k)) p → connection-equality (forward-G (Network.local-wire G (k , p)))
                ; (inj₂ k) p → connection-equality (forward-H (Network.local-wire H (k , p))) } }

  backward : Embedding ((H ∘ G) ∘ F) (H ∘ (G ∘ F))
  backward = record
    { box-map = λ { (inj₁ k) → inj₁ (inj₁ k) ; (inj₂ (inj₁ k)) → inj₁ (inj₂ k) ; (inj₂ (inj₂ k)) → inj₂ k }
    ; box-label = λ { (inj₁ k) → refl ; (inj₂ (inj₁ k)) → refl ; (inj₂ (inj₂ k)) → refl }
    ; name-map = backward-name ; name-type = backward-type ; connected = backward-connected
    ; external = λ _ → S.same
    ; local = λ { (inj₁ k) p → connection-equality (backward-F (Network.local-wire F (k , p)))
                ; (inj₂ (inj₁ k)) p → connection-equality (backward-G (Network.local-wire G (k , p)))
                ; (inj₂ (inj₂ k)) p → connection-equality (backward-H (Network.local-wire H (k , p))) } }

  associative-plugging : (H ∘ (G ∘ F)) ≅ ((H ∘ G) ∘ F)
  associative-plugging = record
    { forward = forward ; backward = backward
    ; boxes-left = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl }
    ; boxes-right = λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    ; names-left = λ n → connection-equality (names-left n)
    ; names-right = λ n → connection-equality (names-right n) }
