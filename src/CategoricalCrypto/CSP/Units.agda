{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Units (Sort : Set) (Payload : Sort → Set) where

open import Data.Empty
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

module RightUnit {A B : Interface} (F : Network A B) where
  module C = Compose F (id {B})
  module S = Wiring (id ∘ F)
  module T = Wiring F
  module P = Plug F (id {B})

  collapse : S.Name → T.Name
  collapse (inj₁ (inj₁ (inj₁ p))) = inj₁ p
  collapse (inj₁ (inj₁ (inj₂ b))) = inj₂ (inj₂ b)
  collapse (inj₁ (inj₂ ()))
  collapse (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
  collapse (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  expand : T.Name → S.Name
  expand (inj₁ p) = inj₁ (inj₁ (inj₁ p))
  expand (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
  expand (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  collapse-left : ∀ n → collapse (C.left n) ≡ n
  collapse-left (inj₁ p) = refl
  collapse-left (inj₂ (inj₁ a)) = refl
  collapse-left (inj₂ (inj₂ b)) = refl

  collapse-expand : ∀ n → collapse (expand n) ≡ n
  collapse-expand (inj₁ p) = refl
  collapse-expand (inj₂ (inj₁ a)) = refl
  collapse-expand (inj₂ (inj₂ b)) = refl

  adjust : ∀ n → S.Connected (expand n) (C.left n)
  adjust (inj₁ p) = S.same
  adjust (inj₂ (inj₁ a)) = S.same
  adjust (inj₂ (inj₂ b)) = S.reverse (P.right-connected (identity-alias b))

  expand-collapse : ∀ n → S.Connected (expand (collapse n)) n
  expand-collapse (inj₁ (inj₁ (inj₁ p))) = S.same
  expand-collapse (inj₁ (inj₁ (inj₂ b))) = adjust (inj₂ (inj₂ b))
  expand-collapse (inj₁ (inj₂ ()))
  expand-collapse (inj₂ (inj₁ a)) = S.same
  expand-collapse (inj₂ (inj₂ b)) = S.same

  collapse-type : ∀ n → S.name-sort n ≡ T.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ (inj₁ p))) = refl
  collapse-type (inj₁ (inj₁ (inj₂ b))) = refl
  collapse-type (inj₁ (inj₂ ()))
  collapse-type (inj₂ (inj₁ a)) = refl
  collapse-type (inj₂ (inj₂ b)) = refl

  expand-type : ∀ n → T.name-sort n ≡ S.name-sort (expand n)
  expand-type (inj₁ p) = refl
  expand-type (inj₂ (inj₁ a)) = refl
  expand-type (inj₂ (inj₂ b)) = refl

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge C.left) (Network.aliases F)
            → T.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge C.left) member
  ... | (u , v) , mem , refl = T.join (connection-equality (collapse-left u))
    (T.join (T.alias mem) (T.reverse (connection-equality (collapse-left v))))

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge C.right) (Network.aliases (id {B}))
             → T.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge C.right) member
  ... | (u , v) , mem , refl with ∈-map⁻ (Identity.edge B) mem
  ... | i , mem′ , refl = T.same

  collapse-connected : ∀ {u v} → S.Connected u v → T.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge C.left) (Network.aliases F)) member))

  expand-connected : ∀ {u v} → T.Connected u v → S.Connected (expand u) (expand v)
  expand-connected {u} {v} conn = S.join (adjust u)
    (S.join (P.left-connected conn) (S.reverse (adjust v)))

  forward : Embedding (id ∘ F) F
  forward = record
    { box-map = λ { (inj₁ k) → k ; (inj₂ ()) }
    ; box-label = λ { (inj₁ k) → refl ; (inj₂ ()) }
    ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
    ; external = λ { (inj₁ _) → T.same ; (inj₂ _) → T.same }
    ; local = λ { (inj₁ k) p → connection-equality (collapse-left (Network.local-wire F (k , p)))
                ; (inj₂ ()) } }

  backward : Embedding F (id ∘ F)
  backward = record
    { box-map = inj₁ ; box-label = λ _ → refl
    ; name-map = expand ; name-type = expand-type ; connected = expand-connected
    ; external = λ { (inj₁ _) → S.same ; (inj₂ _) → S.same }
    ; local = λ k p → adjust (Network.local-wire F (k , p)) }

  identity-plugging : (id ∘ F) ≅ F
  identity-plugging = record
    { forward = forward ; backward = backward
    ; boxes-left = λ { (inj₁ k) → refl ; (inj₂ ()) } ; boxes-right = λ _ → refl
    ; names-left = expand-collapse ; names-right = λ n → connection-equality (collapse-expand n) }

module LeftUnit {A B : Interface} (F : Network A B) where
  module C = Compose (id {A}) F
  module S = Wiring (F ∘ id)
  module T = Wiring F
  module P = Plug (id {A}) F

  collapse : S.Name → T.Name
  collapse (inj₁ (inj₁ (inj₁ ())))
  collapse (inj₁ (inj₁ (inj₂ a))) = inj₂ (inj₁ a)
  collapse (inj₁ (inj₂ p)) = inj₁ p
  collapse (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
  collapse (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  expand : T.Name → S.Name
  expand (inj₁ p) = inj₁ (inj₂ p)
  expand (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
  expand (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  collapse-right : ∀ n → collapse (C.right n) ≡ n
  collapse-right (inj₁ p) = refl
  collapse-right (inj₂ (inj₁ a)) = refl
  collapse-right (inj₂ (inj₂ b)) = refl

  collapse-expand : ∀ n → collapse (expand n) ≡ n
  collapse-expand (inj₁ p) = refl
  collapse-expand (inj₂ (inj₁ a)) = refl
  collapse-expand (inj₂ (inj₂ b)) = refl

  adjust : ∀ n → S.Connected (expand n) (C.right n)
  adjust (inj₁ p) = S.same
  adjust (inj₂ (inj₁ a)) = P.left-connected (identity-alias a)
  adjust (inj₂ (inj₂ b)) = S.same

  expand-collapse : ∀ n → S.Connected (expand (collapse n)) n
  expand-collapse (inj₁ (inj₁ (inj₁ ())))
  expand-collapse (inj₁ (inj₁ (inj₂ a))) = adjust (inj₂ (inj₁ a))
  expand-collapse (inj₁ (inj₂ p)) = S.same
  expand-collapse (inj₂ (inj₁ a)) = S.same
  expand-collapse (inj₂ (inj₂ b)) = S.same

  collapse-type : ∀ n → S.name-sort n ≡ T.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ (inj₁ ())))
  collapse-type (inj₁ (inj₁ (inj₂ a))) = refl
  collapse-type (inj₁ (inj₂ p)) = refl
  collapse-type (inj₂ (inj₁ a)) = refl
  collapse-type (inj₂ (inj₂ b)) = refl

  expand-type : ∀ n → T.name-sort n ≡ S.name-sort (expand n)
  expand-type (inj₁ p) = refl
  expand-type (inj₂ (inj₁ a)) = refl
  expand-type (inj₂ (inj₂ b)) = refl

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge C.left) (Network.aliases (id {A}))
            → T.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge C.left) member
  ... | (u , v) , mem , refl with ∈-map⁻ (Identity.edge A) mem
  ... | i , mem′ , refl = T.same

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge C.right) (Network.aliases F)
             → T.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge C.right) member
  ... | (u , v) , mem , refl = T.join (connection-equality (collapse-right u))
    (T.join (T.alias mem) (T.reverse (connection-equality (collapse-right v))))

  collapse-connected : ∀ {u v} → S.Connected u v → T.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge C.left) (Network.aliases (id {A}))) member))

  expand-connected : ∀ {u v} → T.Connected u v → S.Connected (expand u) (expand v)
  expand-connected {u} {v} conn = S.join (adjust u)
    (S.join (P.right-connected conn) (S.reverse (adjust v)))

  forward : Embedding (F ∘ id) F
  forward = record
    { box-map = λ { (inj₁ ()) ; (inj₂ k) → k }
    ; box-label = λ { (inj₁ ()) ; (inj₂ k) → refl }
    ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
    ; external = λ { (inj₁ _) → T.same ; (inj₂ _) → T.same }
    ; local = λ { (inj₁ ()) ; (inj₂ k) p → connection-equality (collapse-right (Network.local-wire F (k , p))) } }

  backward : Embedding F (F ∘ id)
  backward = record
    { box-map = inj₂ ; box-label = λ _ → refl
    ; name-map = expand ; name-type = expand-type ; connected = expand-connected
    ; external = λ { (inj₁ _) → S.same ; (inj₂ _) → S.same }
    ; local = λ k p → adjust (Network.local-wire F (k , p)) }

  identity-plugging : (F ∘ id) ≅ F
  identity-plugging = record
    { forward = forward ; backward = backward
    ; boxes-left = λ { (inj₁ ()) ; (inj₂ k) → refl } ; boxes-right = λ _ → refl
    ; names-left = expand-collapse ; names-right = λ n → connection-equality (collapse-expand n) }
