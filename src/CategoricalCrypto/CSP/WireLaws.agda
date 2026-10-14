{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.WireLaws (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.FiniteWires Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Wiring Sort Payload

wire-alias : ∀ {A B} (f : PortIso A B) i
  → Wiring.Connected (wire f) (inj₂ (inj₁ i)) (inj₂ (inj₂ (PortIso.to f i)))
wire-alias {A} f i = Wiring.alias (∈-map⁺
  (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (PortIso.to f i))) (enumerate-complete (Interface.shape A) i))

module Composition {A B C : Interface} (f : PortIso A B) (g : PortIso B C) where
  module F = PortIso f
  module G = PortIso g
  module S = Compose (wire f) (wire g)
  module WS = Wiring ((wire g) ∘ (wire f))
  module WT = Wiring (wire (port-compose g f))
  module P = Plug (wire f) (wire g)

  collapse : WS.Name → WT.Name
  collapse (inj₁ (inj₁ (inj₁ ())))
  collapse (inj₁ (inj₁ (inj₂ b))) = inj₂ (inj₂ (G.to b))
  collapse (inj₁ (inj₂ ()))
  collapse (inj₂ e) = inj₂ e

  expand : WT.Name → WS.Name
  expand (inj₁ ())
  expand (inj₂ e) = inj₂ e

  collapse-type : ∀ n → WS.name-sort n ≡ WT.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ (inj₁ ())))
  collapse-type (inj₁ (inj₁ (inj₂ b))) = cong Port.sort (G.typed b)
  collapse-type (inj₁ (inj₂ ()))
  collapse-type (inj₂ (inj₁ a)) = refl
  collapse-type (inj₂ (inj₂ c)) = refl

  expand-type : ∀ n → WT.name-sort n ≡ WS.name-sort (expand n)
  expand-type (inj₁ ())
  expand-type (inj₂ (inj₁ a)) = refl
  expand-type (inj₂ (inj₂ c)) = refl

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.left) (Network.aliases (wire f))
    → WT.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge S.left) member
  ... | (u , v) , mem , refl with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (F.to i))) mem
  ... | i , mem′ , refl = wire-alias (port-compose g f) i

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.right) (Network.aliases (wire g))
    → WT.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge S.right) member
  ... | (u , v) , mem , refl with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (G.to i))) mem
  ... | i , mem′ , refl = WT.same

  collapse-connected : ∀ {u v} → WS.Connected u v → WT.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge S.left) (Network.aliases (wire f))) member))

  expand-edge : ∀ {u v} → (u , v) ∈ Network.aliases (wire (port-compose g f))
    → WS.Connected (expand u) (expand v)
  expand-edge member with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (G.to (F.to i)))) member
  ... | i , mem , refl = WS.join (P.left-connected (wire-alias f i))
    (P.right-connected (wire-alias g (F.to i)))

  expand-connected : ∀ {u v} → WT.Connected u v → WS.Connected (expand u) (expand v)
  expand-connected = map-connected expand expand-edge

  forward : Embedding ((wire g) ∘ (wire f)) (wire (port-compose g f))
  forward = record
    { box-map = λ { (inj₁ ()) ; (inj₂ ()) } ; box-label = λ { (inj₁ ()) ; (inj₂ ()) }
    ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
    ; external = λ _ → WT.same ; local = λ { (inj₁ ()) ; (inj₂ ()) } }

  backward : Embedding (wire (port-compose g f)) ((wire g) ∘ (wire f))
  backward = record
    { box-map = λ () ; box-label = λ () ; name-map = expand ; name-type = expand-type
    ; connected = expand-connected ; external = λ _ → WS.same ; local = λ () }

  names-left : ∀ n → WS.Connected (expand (collapse n)) n
  names-left (inj₁ (inj₁ (inj₁ ())))
  names-left (inj₁ (inj₁ (inj₂ b))) = WS.reverse (P.right-connected (wire-alias g b))
  names-left (inj₁ (inj₂ ()))
  names-left (inj₂ _) = WS.same

  names-right : ∀ n → WT.Connected (collapse (expand n)) n
  names-right (inj₁ ())
  names-right (inj₂ _) = WT.same

  compose-wires : ((wire g) ∘ (wire f)) ≅ wire (port-compose g f)
  compose-wires = record
    { forward = forward ; backward = backward
    ; boxes-left = λ { (inj₁ ()) ; (inj₂ ()) } ; boxes-right = λ ()
    ; names-left = names-left ; names-right = names-right }

wire-id : ∀ A → wire (port-id A) ≅ id
wire-id A = record
  { forward = record
      { box-map = λ () ; box-label = λ () ; name-map = λ n → n
      ; name-type = λ { (inj₁ ()) ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
      ; connected = map-connected (λ n → n) (λ a → Wiring.alias a)
      ; external = λ _ → Wiring.same ; local = λ () }
  ; backward = record
      { box-map = λ () ; box-label = λ () ; name-map = λ n → n
      ; name-type = λ { (inj₁ ()) ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
      ; connected = map-connected (λ n → n) (λ a → Wiring.alias a)
      ; external = λ _ → Wiring.same ; local = λ () }
  ; boxes-left = λ () ; boxes-right = λ ()
  ; names-left = λ _ → Wiring.same ; names-right = λ _ → Wiring.same }

module Extensional {A B : Interface} (f g : PortIso A B) (equal : ∀ i → PortIso.to f i ≡ PortIso.to g i) where
  module WF = Wiring (wire f)
  module WG = Wiring (wire g)

  forward-edge : ∀ {u v} → (u , v) ∈ Network.aliases (wire f) → WG.Connected u v
  forward-edge member with ∈-map⁻ (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (PortIso.to f i))) member
  ... | i , mem , refl = WG.join (wire-alias g i)
    (connection-equality (cong (λ j → inj₂ (inj₂ j)) (sym (equal i))))

  backward-edge : ∀ {u v} → (u , v) ∈ Network.aliases (wire g) → WF.Connected u v
  backward-edge member with ∈-map⁻ (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (PortIso.to g i))) member
  ... | i , mem , refl = WF.join (wire-alias f i)
    (connection-equality (cong (λ j → inj₂ (inj₂ j)) (equal i)))

  wire-resp : wire f ≅ wire g
  wire-resp = record
    { forward = record
        { box-map = λ () ; box-label = λ () ; name-map = λ n → n
        ; name-type = λ { (inj₁ ()) ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
        ; connected = map-connected (λ n → n) forward-edge
        ; external = λ _ → WG.same ; local = λ () }
    ; backward = record
        { box-map = λ () ; box-label = λ () ; name-map = λ n → n
        ; name-type = λ { (inj₁ ()) ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
        ; connected = map-connected (λ n → n) backward-edge
        ; external = λ _ → WF.same ; local = λ () }
    ; boxes-left = λ () ; boxes-right = λ ()
    ; names-left = λ _ → WF.same ; names-right = λ _ → WG.same }

module TensorWires {A B C D : Interface} (f : PortIso A B) (g : PortIso C D) where
  module F = PortIso f
  module G = PortIso g
  module T = Tensor (wire f) (wire g)
  module WS = Wiring ((wire f) ⊗₁ (wire g))
  module WT = Wiring (wire (port-tensor f g))
  module P = Disjoint (wire f) (wire g)

  collapse : WS.Name → WT.Name
  collapse (inj₁ (inj₁ ()))
  collapse (inj₁ (inj₂ ()))
  collapse (inj₂ e) = inj₂ e
  expand : WT.Name → WS.Name
  expand (inj₁ ())
  expand (inj₂ e) = inj₂ e

  collapse-type : ∀ n → WS.name-sort n ≡ WT.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ ()))
  collapse-type (inj₁ (inj₂ ()))
  collapse-type (inj₂ (inj₁ (inj₁ _))) = refl
  collapse-type (inj₂ (inj₁ (inj₂ _))) = refl
  collapse-type (inj₂ (inj₂ (inj₁ _))) = refl
  collapse-type (inj₂ (inj₂ (inj₂ _))) = refl
  expand-type : ∀ n → WT.name-sort n ≡ WS.name-sort (expand n)
  expand-type (inj₁ ())
  expand-type (inj₂ (inj₁ (inj₁ _))) = refl
  expand-type (inj₂ (inj₁ (inj₂ _))) = refl
  expand-type (inj₂ (inj₂ (inj₁ _))) = refl
  expand-type (inj₂ (inj₂ (inj₂ _))) = refl

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge T.left) (Network.aliases (wire f))
    → WT.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge T.left) member
  ... | (u , v) , mem , refl with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (F.to i))) mem
  ... | i , mem′ , refl = wire-alias (port-tensor f g) (inj₁ i)
  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge T.right) (Network.aliases (wire g))
    → WT.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge T.right) member
  ... | (u , v) , mem , refl with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (G.to i))) mem
  ... | i , mem′ , refl = wire-alias (port-tensor f g) (inj₂ i)

  collapse-connected : ∀ {u v} → WS.Connected u v → WT.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge T.left) (Network.aliases (wire f))) member))

  expand-edge : ∀ {u v} → (u , v) ∈ Network.aliases (wire (port-tensor f g))
    → WS.Connected (expand u) (expand v)
  expand-edge member with ∈-map⁻
    (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (PortIso.to (port-tensor f g) i))) member
  ... | inj₁ i , mem , refl = P.left-connected (wire-alias f i)
  ... | inj₂ i , mem , refl = P.right-connected (wire-alias g i)

  expand-connected : ∀ {u v} → WT.Connected u v → WS.Connected (expand u) (expand v)
  expand-connected = map-connected expand expand-edge

  tensor-wires : ((wire f) ⊗₁ (wire g)) ≅ wire (port-tensor f g)
  tensor-wires = record
    { forward = record
        { box-map = λ { (inj₁ ()) ; (inj₂ ()) } ; box-label = λ { (inj₁ ()) ; (inj₂ ()) }
        ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
        ; external = λ _ → WT.same ; local = λ { (inj₁ ()) ; (inj₂ ()) } }
    ; backward = record
        { box-map = λ () ; box-label = λ () ; name-map = expand ; name-type = expand-type
        ; connected = expand-connected ; external = λ _ → WS.same ; local = λ () }
    ; boxes-left = λ { (inj₁ ()) ; (inj₂ ()) } ; boxes-right = λ ()
    ; names-left = λ { (inj₁ (inj₁ ())) ; (inj₁ (inj₂ ())) ; (inj₂ _) → WS.same }
    ; names-right = λ { (inj₁ ()) ; (inj₂ _) → WT.same } }
