{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Congruence (Sort : Set) (Payload : Sort → Set) where

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

module PlugEmbedding {A B C : Interface} {F F′ : Network A B} {G G′ : Network B C}
  (f : Embedding F F′) (g : Embedding G G′) where
  module F = Embedding f
  module G = Embedding g
  module S = Compose F G
  module T = Compose F′ G′
  module WT = Wiring (G′ ∘ F′)
  module ST = Plug F G
  module TT = Plug F′ G′

  name-map : Wiring.Name (G ∘ F) → WT.Name
  name-map (inj₁ (inj₁ (inj₁ p))) = T.left (F.name-map (inj₁ p))
  name-map (inj₁ (inj₁ (inj₂ b))) = inj₁ (inj₁ (inj₂ b))
  name-map (inj₁ (inj₂ p)) = T.right (G.name-map (inj₁ p))
  name-map (inj₂ e) = inj₂ e

  name-type : ∀ n → Wiring.name-sort (G ∘ F) n ≡ WT.name-sort (name-map n)
  name-type (inj₁ (inj₁ (inj₁ p))) = trans (F.name-type (inj₁ p)) (sym (T.left-type (F.name-map (inj₁ p))))
  name-type (inj₁ (inj₁ (inj₂ b))) = refl
  name-type (inj₁ (inj₂ p)) = trans (G.name-type (inj₁ p)) (sym (T.right-type (G.name-map (inj₁ p))))
  name-type (inj₂ (inj₁ a)) = refl
  name-type (inj₂ (inj₂ c)) = refl

  align-left : ∀ n → WT.Connected (name-map (S.left n)) (T.left (F.name-map n))
  align-left (inj₁ p) = WT.same
  align-left (inj₂ (inj₁ a)) = WT.reverse (TT.left-connected (F.external (inj₁ a)))
  align-left (inj₂ (inj₂ b)) = WT.reverse (TT.left-connected (F.external (inj₂ b)))

  align-right : ∀ n → WT.Connected (name-map (S.right n)) (T.right (G.name-map n))
  align-right (inj₁ p) = WT.same
  align-right (inj₂ (inj₁ b)) = WT.reverse (TT.right-connected (G.external (inj₁ b)))
  align-right (inj₂ (inj₂ c)) = WT.reverse (TT.right-connected (G.external (inj₂ c)))

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.left) (Network.aliases F)
    → WT.Connected (name-map u) (name-map v)
  left-edge member with ∈-map⁻ (map-edge S.left) member
  ... | (u , v) , mem , refl = WT.join (align-left u)
    (WT.join (TT.left-connected (F.connected (Wiring.alias mem))) (WT.reverse (align-left v)))

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.right) (Network.aliases G)
    → WT.Connected (name-map u) (name-map v)
  right-edge member with ∈-map⁻ (map-edge S.right) member
  ... | (u , v) , mem , refl = WT.join (align-right u)
    (WT.join (TT.right-connected (G.connected (Wiring.alias mem))) (WT.reverse (align-right v)))

  connected : ∀ {u v} → Wiring.Connected (G ∘ F) u v → WT.Connected (name-map u) (name-map v)
  connected = map-connected name-map (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge S.left) (Network.aliases F)) member))

  embedding : Embedding (G ∘ F) (G′ ∘ F′)
  embedding = record
    { box-map = λ { (inj₁ k) → inj₁ (F.box-map k) ; (inj₂ k) → inj₂ (G.box-map k) }
    ; box-label = λ { (inj₁ k) → F.box-label k ; (inj₂ k) → G.box-label k }
    ; name-map = name-map ; name-type = name-type ; connected = connected
    ; external = λ _ → WT.same
    ; local = λ { (inj₁ k) p → WT.join (align-left (Network.local-wire F (k , p))) (TT.left-connected (F.local k p))
                ; (inj₂ k) p → WT.join (align-right (Network.local-wire G (k , p))) (TT.right-connected (G.local k p)) } }

module PlugIso {A B C : Interface} {F F′ : Network A B} {G G′ : Network B C}
  (f : F ≅ F′) (g : G ≅ G′) where
  module F = _≅_ f
  module G = _≅_ g
  module FF = Embedding F.forward
  module GF = Embedding G.forward
  module FB = Embedding F.backward
  module GB = Embedding G.backward
  module P = PlugEmbedding F.forward G.forward
  module Q = PlugEmbedding F.backward G.backward
  module WS = Wiring (G ∘ F)
  module WT = Wiring (G′ ∘ F′)
  module S = Plug F G
  module T = Plug F′ G′

  names-left : ∀ n → WS.Connected (Q.name-map (P.name-map n)) n
  names-left (inj₁ (inj₁ (inj₁ p))) = WS.join (Q.align-left (FF.name-map (inj₁ p)))
    (S.left-connected (F.names-left (inj₁ p)))
  names-left (inj₁ (inj₁ (inj₂ b))) = WS.same
  names-left (inj₁ (inj₂ p)) = WS.join (Q.align-right (GF.name-map (inj₁ p)))
    (S.right-connected (G.names-left (inj₁ p)))
  names-left (inj₂ _) = WS.same

  names-right : ∀ n → WT.Connected (P.name-map (Q.name-map n)) n
  names-right (inj₁ (inj₁ (inj₁ p))) = WT.join (P.align-left (FB.name-map (inj₁ p)))
    (T.left-connected (F.names-right (inj₁ p)))
  names-right (inj₁ (inj₁ (inj₂ b))) = WT.same
  names-right (inj₁ (inj₂ p)) = WT.join (P.align-right (GB.name-map (inj₁ p)))
    (T.right-connected (G.names-right (inj₁ p)))
  names-right (inj₂ _) = WT.same

  plugging-congruence : (G ∘ F) ≅ (G′ ∘ F′)
  plugging-congruence = record
    { forward = P.embedding ; backward = Q.embedding
    ; boxes-left = λ { (inj₁ k) → cong inj₁ (F.boxes-left k) ; (inj₂ k) → cong inj₂ (G.boxes-left k) }
    ; boxes-right = λ { (inj₁ k) → cong inj₁ (F.boxes-right k) ; (inj₂ k) → cong inj₂ (G.boxes-right k) }
    ; names-left = names-left ; names-right = names-right }

module TensorEmbedding {A B C D : Interface} {F F′ : Network A B} {G G′ : Network C D}
  (f : Embedding F F′) (g : Embedding G G′) where
  module F = Embedding f
  module G = Embedding g
  module S = Tensor F G
  module T = Tensor F′ G′
  module WT = Wiring (F′ ⊗₁ G′)
  module TT = Disjoint F′ G′

  name-map : Wiring.Name (F ⊗₁ G) → WT.Name
  name-map (inj₁ (inj₁ p)) = T.left (F.name-map (inj₁ p))
  name-map (inj₁ (inj₂ p)) = T.right (G.name-map (inj₁ p))
  name-map (inj₂ e) = inj₂ e

  name-type : ∀ n → Wiring.name-sort (F ⊗₁ G) n ≡ WT.name-sort (name-map n)
  name-type (inj₁ (inj₁ p)) = trans (F.name-type (inj₁ p)) (sym (T.left-type (F.name-map (inj₁ p))))
  name-type (inj₁ (inj₂ p)) = trans (G.name-type (inj₁ p)) (sym (T.right-type (G.name-map (inj₁ p))))
  name-type (inj₂ (inj₁ (inj₁ a))) = refl
  name-type (inj₂ (inj₁ (inj₂ c))) = refl
  name-type (inj₂ (inj₂ (inj₁ b))) = refl
  name-type (inj₂ (inj₂ (inj₂ d))) = refl

  align-left : ∀ n → WT.Connected (name-map (S.left n)) (T.left (F.name-map n))
  align-left (inj₁ p) = WT.same
  align-left (inj₂ (inj₁ a)) = WT.reverse (TT.left-connected (F.external (inj₁ a)))
  align-left (inj₂ (inj₂ b)) = WT.reverse (TT.left-connected (F.external (inj₂ b)))

  align-right : ∀ n → WT.Connected (name-map (S.right n)) (T.right (G.name-map n))
  align-right (inj₁ p) = WT.same
  align-right (inj₂ (inj₁ c)) = WT.reverse (TT.right-connected (G.external (inj₁ c)))
  align-right (inj₂ (inj₂ d)) = WT.reverse (TT.right-connected (G.external (inj₂ d)))

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.left) (Network.aliases F)
    → WT.Connected (name-map u) (name-map v)
  left-edge member with ∈-map⁻ (map-edge S.left) member
  ... | (u , v) , mem , refl = WT.join (align-left u)
    (WT.join (TT.left-connected (F.connected (Wiring.alias mem))) (WT.reverse (align-left v)))

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.right) (Network.aliases G)
    → WT.Connected (name-map u) (name-map v)
  right-edge member with ∈-map⁻ (map-edge S.right) member
  ... | (u , v) , mem , refl = WT.join (align-right u)
    (WT.join (TT.right-connected (G.connected (Wiring.alias mem))) (WT.reverse (align-right v)))

  connected : ∀ {u v} → Wiring.Connected (F ⊗₁ G) u v → WT.Connected (name-map u) (name-map v)
  connected = map-connected name-map (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge S.left) (Network.aliases F)) member))

  embedding : Embedding (F ⊗₁ G) (F′ ⊗₁ G′)
  embedding = record
    { box-map = λ { (inj₁ k) → inj₁ (F.box-map k) ; (inj₂ k) → inj₂ (G.box-map k) }
    ; box-label = λ { (inj₁ k) → F.box-label k ; (inj₂ k) → G.box-label k }
    ; name-map = name-map ; name-type = name-type ; connected = connected
    ; external = λ _ → WT.same
    ; local = λ { (inj₁ k) p → WT.join (align-left (Network.local-wire F (k , p))) (TT.left-connected (F.local k p))
                ; (inj₂ k) p → WT.join (align-right (Network.local-wire G (k , p))) (TT.right-connected (G.local k p)) } }

module TensorIso {A B C D : Interface} {F F′ : Network A B} {G G′ : Network C D}
  (f : F ≅ F′) (g : G ≅ G′) where
  module F = _≅_ f
  module G = _≅_ g
  module FF = Embedding F.forward
  module GF = Embedding G.forward
  module FB = Embedding F.backward
  module GB = Embedding G.backward
  module P = TensorEmbedding F.forward G.forward
  module Q = TensorEmbedding F.backward G.backward
  module WS = Wiring (F ⊗₁ G)
  module WT = Wiring (F′ ⊗₁ G′)
  module S = Disjoint F G
  module T = Disjoint F′ G′

  names-left : ∀ n → WS.Connected (Q.name-map (P.name-map n)) n
  names-left (inj₁ (inj₁ p)) = WS.join (Q.align-left (FF.name-map (inj₁ p)))
    (S.left-connected (F.names-left (inj₁ p)))
  names-left (inj₁ (inj₂ p)) = WS.join (Q.align-right (GF.name-map (inj₁ p)))
    (S.right-connected (G.names-left (inj₁ p)))
  names-left (inj₂ _) = WS.same

  names-right : ∀ n → WT.Connected (P.name-map (Q.name-map n)) n
  names-right (inj₁ (inj₁ p)) = WT.join (P.align-left (FB.name-map (inj₁ p)))
    (T.left-connected (F.names-right (inj₁ p)))
  names-right (inj₁ (inj₂ p)) = WT.join (P.align-right (GB.name-map (inj₁ p)))
    (T.right-connected (G.names-right (inj₁ p)))
  names-right (inj₂ _) = WT.same

  tensor-congruence : (F ⊗₁ G) ≅ (F′ ⊗₁ G′)
  tensor-congruence = record
    { forward = P.embedding ; backward = Q.embedding
    ; boxes-left = λ { (inj₁ k) → cong inj₁ (F.boxes-left k) ; (inj₂ k) → cong inj₂ (G.boxes-left k) }
    ; boxes-right = λ { (inj₁ k) → cong inj₁ (F.boxes-right k) ; (inj₂ k) → cong inj₂ (G.boxes-right k) }
    ; names-left = names-left ; names-right = names-right }
