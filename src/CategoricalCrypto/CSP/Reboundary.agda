{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Reboundary (Sort : Set) (Payload : Sort → Set) where

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.FiniteWires Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.WireLaws Sort Payload
open import CategoricalCrypto.CSP.Wiring Sort Payload

open Interface
open Port

module Relabel {A A′ B B′ : Interface} (a : PortIso A A′) (b : PortIso B B′) (N : Network A B) where
  module A = PortIso a
  module B = PortIso b
  module N = Network N
  module W = Wiring N

  Name : Set
  Name = ⟨ N.private-shape ⟩ ⊎ (⟨ shape A′ ⟩ ⊎ ⟨ shape B′ ⟩)

  name-sort : Name → Sort
  name-sort = [ N.private-sort , [ (λ i → sort (ports A′ i)) , (λ i → sort (ports B′ i)) ]′ ]′

  rename : W.Name → Name
  rename (inj₁ p) = inj₁ p
  rename (inj₂ (inj₁ i)) = inj₂ (inj₁ (A.to i))
  rename (inj₂ (inj₂ i)) = inj₂ (inj₂ (B.to i))

  typed : ∀ n → W.name-sort n ≡ name-sort (rename n)
  typed (inj₁ p) = refl
  typed (inj₂ (inj₁ i)) = cong sort (A.typed i)
  typed (inj₂ (inj₂ i)) = cong sort (B.typed i)

  rewire : Network A′ B′
  rewire = mkNetwork N.components N.private-shape N.private-sort
    (λ kp → rename (N.local-wire kp))
    (λ kp → trans (N.wire-type kp) (typed (N.local-wire kp)))
    (map (map-edge rename) N.aliases)
    (map-edge-typed rename (λ n → sym (typed n)) N.aliases N.alias-type)

module Post {A B C : Interface} (N : Network A B) (b : PortIso B C) where
  module B = PortIso b
  module R = Relabel (port-id A) b N
  module S = Compose N (wire b)
  module WS = Wiring ((wire b) ∘ N)
  module WT = Wiring R.rewire
  module P = Plug N (wire b)

  collapse : WS.Name → WT.Name
  collapse (inj₁ (inj₁ (inj₁ p))) = inj₁ p
  collapse (inj₁ (inj₁ (inj₂ i))) = inj₂ (inj₂ (B.to i))
  collapse (inj₁ (inj₂ ()))
  collapse (inj₂ e) = inj₂ e
  expand : WT.Name → WS.Name
  expand (inj₁ p) = inj₁ (inj₁ (inj₁ p))
  expand (inj₂ e) = inj₂ e

  collapse-left : ∀ n → collapse (S.left n) ≡ R.rename n
  collapse-left (inj₁ _) = refl
  collapse-left (inj₂ (inj₁ _)) = refl
  collapse-left (inj₂ (inj₂ _)) = refl

  collapse-type : ∀ n → WS.name-sort n ≡ WT.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ (inj₁ _))) = refl
  collapse-type (inj₁ (inj₁ (inj₂ i))) = cong sort (B.typed i)
  collapse-type (inj₁ (inj₂ ()))
  collapse-type (inj₂ (inj₁ _)) = refl
  collapse-type (inj₂ (inj₂ _)) = refl
  expand-type : ∀ n → WT.name-sort n ≡ WS.name-sort (expand n)
  expand-type (inj₁ _) = refl
  expand-type (inj₂ (inj₁ _)) = refl
  expand-type (inj₂ (inj₂ _)) = refl

  renamed-edge : ∀ {u v} → (u , v) ∈ Network.aliases N → WT.Connected (R.rename u) (R.rename v)
  renamed-edge edge = WT.alias (∈-map⁺ (map-edge R.rename) edge)

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.left) (Network.aliases N)
    → WT.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge S.left) member
  ... | (u , v) , edge , refl = WT.join (connection-equality (collapse-left u))
    (WT.join (renamed-edge edge) (WT.reverse (connection-equality (collapse-left v))))
  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.right) (Network.aliases (wire b))
    → WT.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge S.right) member
  ... | (u , v) , edge , refl with ∈-map⁻ (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (B.to i))) edge
  ... | i , mem , refl = WT.same

  collapse-connected : ∀ {u v} → WS.Connected u v → WT.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge S.left) (Network.aliases N)) member))

  adjust : ∀ n → WS.Connected (expand (R.rename n)) (S.left n)
  adjust (inj₁ _) = WS.same
  adjust (inj₂ (inj₁ _)) = WS.same
  adjust (inj₂ (inj₂ i)) = WS.reverse (P.right-connected (wire-alias b i))

  expand-edge : ∀ {u v} → (u , v) ∈ Network.aliases R.rewire → WS.Connected (expand u) (expand v)
  expand-edge member with ∈-map⁻ (map-edge R.rename) member
  ... | (u , v) , edge , refl = WS.join (adjust u)
    (WS.join (P.left-connected (Wiring.alias edge)) (WS.reverse (adjust v)))
  expand-connected : ∀ {u v} → WT.Connected u v → WS.Connected (expand u) (expand v)
  expand-connected = map-connected expand expand-edge

  opaque
    post-wire : ((wire b) ∘ N) ≅ R.rewire
    post-wire = record
      { forward = record
          { box-map = λ { (inj₁ k) → k ; (inj₂ ()) } ; box-label = λ { (inj₁ _) → refl ; (inj₂ ()) }
          ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
          ; external = λ _ → WT.same
          ; local = λ { (inj₁ k) p → connection-equality (collapse-left (Network.local-wire N (k , p))) ; (inj₂ ()) } }
      ; backward = record
          { box-map = inj₁ ; box-label = λ _ → refl ; name-map = expand ; name-type = expand-type
          ; connected = expand-connected ; external = λ _ → WS.same ; local = λ k p → adjust (Network.local-wire N (k , p)) }
      ; boxes-left = λ { (inj₁ _) → refl ; (inj₂ ()) } ; boxes-right = λ _ → refl
      ; names-left = λ { (inj₁ (inj₁ (inj₁ _))) → WS.same
                       ; (inj₁ (inj₁ (inj₂ i))) → WS.reverse (P.right-connected (wire-alias b i))
                       ; (inj₁ (inj₂ ())) ; (inj₂ _) → WS.same }
      ; names-right = λ { (inj₁ _) → WT.same ; (inj₂ _) → WT.same } }

module Pre {A B C : Interface} (a : PortIso A B) (N : Network B C) where
  module A = PortIso a
  module R = Relabel (port-inverse a) (port-id C) N
  module S = Compose (wire a) N
  module WS = Wiring (N ∘ wire a)
  module WT = Wiring R.rewire
  module P = Plug (wire a) N

  collapse : WS.Name → WT.Name
  collapse (inj₁ (inj₁ (inj₁ ())))
  collapse (inj₁ (inj₁ (inj₂ i))) = inj₂ (inj₁ (A.from i))
  collapse (inj₁ (inj₂ p)) = inj₁ p
  collapse (inj₂ e) = inj₂ e
  expand : WT.Name → WS.Name
  expand (inj₁ p) = inj₁ (inj₂ p)
  expand (inj₂ e) = inj₂ e

  collapse-right : ∀ n → collapse (S.right n) ≡ R.rename n
  collapse-right (inj₁ _) = refl
  collapse-right (inj₂ (inj₁ _)) = refl
  collapse-right (inj₂ (inj₂ _)) = refl

  collapse-type : ∀ n → WS.name-sort n ≡ WT.name-sort (collapse n)
  collapse-type (inj₁ (inj₁ (inj₁ ())))
  collapse-type (inj₁ (inj₁ (inj₂ i))) = cong sort (PortIso.typed (port-inverse a) i)
  collapse-type (inj₁ (inj₂ _)) = refl
  collapse-type (inj₂ (inj₁ _)) = refl
  collapse-type (inj₂ (inj₂ _)) = refl
  expand-type : ∀ n → WT.name-sort n ≡ WS.name-sort (expand n)
  expand-type (inj₁ _) = refl
  expand-type (inj₂ (inj₁ _)) = refl
  expand-type (inj₂ (inj₂ _)) = refl

  adjust : ∀ i → WS.Connected (inj₂ (inj₁ (A.from i))) (S.right (inj₂ (inj₁ i)))
  adjust i = WS.join (P.left-connected (wire-alias a (A.from i)))
    (connection-equality (cong (λ j → S.right (inj₂ (inj₁ j))) (A.right i)))

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.left) (Network.aliases (wire a))
    → WT.Connected (collapse u) (collapse v)
  left-edge member with ∈-map⁻ (map-edge S.left) member
  ... | (u , v) , edge , refl with ∈-map⁻ (λ i → inj₂ (inj₁ i) , inj₂ (inj₂ (A.to i))) edge
  ... | i , mem , refl = connection-equality (cong (λ j → inj₂ (inj₁ j)) (sym (A.left i)))
  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge S.right) (Network.aliases N)
    → WT.Connected (collapse u) (collapse v)
  right-edge member with ∈-map⁻ (map-edge S.right) member
  ... | (u , v) , edge , refl = WT.join (connection-equality (collapse-right u))
    (WT.join (WT.alias (∈-map⁺ (map-edge R.rename) edge))
      (WT.reverse (connection-equality (collapse-right v))))
  collapse-connected : ∀ {u v} → WS.Connected u v → WT.Connected (collapse u) (collapse v)
  collapse-connected = map-connected collapse (λ member → [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge S.left) (Network.aliases (wire a))) member))

  expand-right : ∀ n → WS.Connected (expand (R.rename n)) (S.right n)
  expand-right (inj₁ _) = WS.same
  expand-right (inj₂ (inj₁ i)) = adjust i
  expand-right (inj₂ (inj₂ _)) = WS.same
  expand-edge : ∀ {u v} → (u , v) ∈ Network.aliases R.rewire → WS.Connected (expand u) (expand v)
  expand-edge member with ∈-map⁻ (map-edge R.rename) member
  ... | (u , v) , edge , refl = WS.join (expand-right u)
    (WS.join (P.right-connected (Wiring.alias edge)) (WS.reverse (expand-right v)))
  expand-connected : ∀ {u v} → WT.Connected u v → WS.Connected (expand u) (expand v)
  expand-connected = map-connected expand expand-edge

  opaque
    pre-wire : (N ∘ wire a) ≅ R.rewire
    pre-wire = record
      { forward = record
          { box-map = λ { (inj₁ ()) ; (inj₂ k) → k } ; box-label = λ { (inj₁ ()) ; (inj₂ _) → refl }
          ; name-map = collapse ; name-type = collapse-type ; connected = collapse-connected
          ; external = λ _ → WT.same
          ; local = λ { (inj₁ ()) ; (inj₂ k) p → connection-equality (collapse-right (Network.local-wire N (k , p))) } }
      ; backward = record
          { box-map = inj₂ ; box-label = λ _ → refl ; name-map = expand ; name-type = expand-type
          ; connected = expand-connected ; external = λ _ → WS.same
          ; local = λ k p → expand-right (Network.local-wire N (k , p)) }
      ; boxes-left = λ { (inj₁ ()) ; (inj₂ _) → refl } ; boxes-right = λ _ → refl
      ; names-left = λ { (inj₁ (inj₁ (inj₁ ()))) ; (inj₁ (inj₁ (inj₂ i))) → adjust i
                       ; (inj₁ (inj₂ _)) → WS.same ; (inj₂ _) → WS.same }
      ; names-right = λ { (inj₁ _) → WT.same ; (inj₂ _) → WT.same } }

-- Reason over graph variables before specializing to nested tensor graphs.
module WireSquare {A B C D : Interface} (a : PortIso A B) (b : PortIso C D)
  (N : Network A C) (M : Network B D) where
  module S = Relabel (port-id A) b N
  module T = Relabel (port-inverse a) (port-id D) M

  opaque
    commute : S.rewire ≅ T.rewire → (wire b ∘ N) ≅ (M ∘ wire a)
    commute retag = ≅-trans (Post.post-wire N b)
      (≅-trans retag (≅-sym (Pre.pre-wire a M)))

  opaque
    inverse-commute :
      Morphism.Iso OpenCSP (wire a) (wire (port-inverse a)) →
      Morphism.Iso OpenCSP (wire b) (wire (port-inverse b)) →
      (wire b ∘ N) ≅ (M ∘ wire a) →
      (wire (port-inverse b) ∘ M) ≅ (N ∘ wire (port-inverse a))
    inverse-commute a-iso b-iso square = MorphismReasoning.conjugate-from OpenCSP
      (record { from = wire a ; to = wire (port-inverse a) ; iso = a-iso })
      (record { from = wire b ; to = wire (port-inverse b) ; iso = b-iso })
      {f = M} {g = N} (≅-sym square)
