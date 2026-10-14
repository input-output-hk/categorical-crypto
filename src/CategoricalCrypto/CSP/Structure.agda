{-# OPTIONS --safe --without-K --guardedness #-}

-- Names are compared modulo finite alias connectivity; boxes and their native
-- labels are retained exactly. This is not a failures/divergences quotient.
module CategoricalCrypto.CSP.Structure (Sort : Set) (Payload : Sort → Set) where

open import Data.Product.Base
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload

open Interface
open Component
open Boxes renaming (shape to box-shape)

PortIndex : Component → Set
PortIndex c = ⟨ shape (boundary c) ⟩

cast-port : ∀ {c d} → c ≡ d → PortIndex c → PortIndex d
cast-port refl p = p

cast-port-compose : ∀ {a b c} (p : a ≡ b) (q : b ≡ c) i
                  → cast-port (trans p q) i ≡ cast-port q (cast-port p i)
cast-port-compose refl refl i = refl

record Embedding {A B : Interface} (F G : Network A B) : Set₁ where
  module F = Network F
  module G = Network G
  module WF = Wiring F
  module WG = Wiring G
  field
    box-map : ⟨ box-shape F.components ⟩ → ⟨ box-shape G.components ⟩
    box-label : ∀ k → label F.components k ≡ label G.components (box-map k)
    name-map : WF.Name → WG.Name
    name-type : ∀ n → WF.name-sort n ≡ WG.name-sort (name-map n)
    connected : ∀ {u v} → WF.Connected u v → WG.Connected (name-map u) (name-map v)
    external : ∀ e → WG.Connected (name-map (inj₂ e)) (inj₂ e)
    local : ∀ k p → WG.Connected (name-map (F.local-wire (k , p)))
      (G.local-wire (box-map k , cast-port (box-label k) p))

infix 4 _≅_
record _≅_ {A B : Interface} (F G : Network A B) : Set₁ where
  module WF = Wiring F
  module WG = Wiring G
  field
    forward : Embedding F G
    backward : Embedding G F
  module F = Embedding forward
  module G = Embedding backward
  field
    boxes-left : ∀ k → G.box-map (F.box-map k) ≡ k
    boxes-right : ∀ k → F.box-map (G.box-map k) ≡ k
    names-left : ∀ n → WF.Connected (G.name-map (F.name-map n)) n
    names-right : ∀ n → WG.Connected (F.name-map (G.name-map n)) n

identity-embedding : ∀ {A B} {F : Network A B} → Embedding F F
identity-embedding = record
  { box-map = λ k → k ; box-label = λ _ → refl
  ; name-map = λ n → n ; name-type = λ _ → refl
  ; connected = λ p → p ; external = λ _ → Wiring.same ; local = λ _ _ → Wiring.same }

≅-refl : ∀ {A B} {F : Network A B} → F ≅ F
≅-refl = record
  { forward = identity-embedding ; backward = identity-embedding
  ; boxes-left = λ _ → refl ; boxes-right = λ _ → refl
  ; names-left = λ _ → Wiring.same ; names-right = λ _ → Wiring.same }

≅-sym : ∀ {A B} {F G : Network A B} → F ≅ G → G ≅ F
≅-sym iso = record
  { forward = forward ; backward = backward
  ; boxes-left = boxes-left ; boxes-right = boxes-right
  ; names-left = names-left ; names-right = names-right }
  where
    open _≅_ iso renaming
      (forward to backward; backward to forward; boxes-left to boxes-right; boxes-right to boxes-left
      ; names-left to names-right; names-right to names-left)

connection-equality : ∀ {A B} {N : Network A B} {u v} → u ≡ v → Wiring.Connected N u v
connection-equality refl = Wiring.same

compose-embedding : ∀ {A B} {F G H : Network A B}
                  → Embedding G H → Embedding F G → Embedding F H
compose-embedding {H = H} second first = record
  { box-map = λ k → S.box-map (F.box-map k)
  ; box-label = λ k → trans (F.box-label k) (S.box-label (F.box-map k))
  ; name-map = λ n → S.name-map (F.name-map n)
  ; name-type = λ n → trans (F.name-type n) (S.name-type (F.name-map n))
  ; connected = λ p → S.connected (F.connected p)
  ; external = λ e → W.join (S.connected (F.external e)) (S.external e)
  ; local = λ k p → W.join (S.connected (F.local k p))
      (W.join (S.local (F.box-map k) (cast-port (F.box-label k) p))
        (connection-equality (cong (λ z → Network.local-wire H (S.box-map (F.box-map k) , z))
          (sym (cast-port-compose (F.box-label k) (S.box-label (F.box-map k)) p))))) }
  where
    module F = Embedding first
    module S = Embedding second
    module W = Wiring H

≅-trans : ∀ {A B} {F G H : Network A B} → F ≅ G → G ≅ H → F ≅ H
≅-trans {F = F} {H = H} first second = record
  { forward = compose-embedding S.forward P.forward
  ; backward = compose-embedding P.backward S.backward
  ; boxes-left = λ k → trans (cong PB.box-map (S.boxes-left (PF.box-map k))) (P.boxes-left k)
  ; boxes-right = λ k → trans (cong SF.box-map (P.boxes-right (SB.box-map k))) (S.boxes-right k)
  ; names-left = λ n → WF.join (PB.connected (S.names-left (PF.name-map n))) (P.names-left n)
  ; names-right = λ n → WH.join (SF.connected (P.names-right (SB.name-map n))) (S.names-right n) }
  where
    module P = _≅_ first
    module S = _≅_ second
    module PF = Embedding P.forward
    module PB = Embedding P.backward
    module SF = Embedding S.forward
    module SB = Embedding S.backward
    module WF = Wiring F
    module WH = Wiring H
