{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Separation (Sort : Set) (Payload : Sort → Set) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Maybe.Base hiding (map)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload

module Disjoint {A B C D : Interface} (F : Network A B) (G : Network C D) where
  module T = Tensor F G
  module W = Wiring (F ⊗₁ G)
  module E = Execution (F ⊗₁ G)

  side : W.Name → Bool
  side (inj₁ (inj₁ _)) = false
  side (inj₁ (inj₂ _)) = true
  side (inj₂ (inj₁ (inj₁ _))) = false
  side (inj₂ (inj₁ (inj₂ _))) = true
  side (inj₂ (inj₂ (inj₁ _))) = false
  side (inj₂ (inj₂ (inj₂ _))) = true

  left-side : ∀ n → side (T.left n) ≡ false
  left-side (inj₁ _) = refl
  left-side (inj₂ (inj₁ _)) = refl
  left-side (inj₂ (inj₂ _)) = refl

  right-side : ∀ n → side (T.right n) ≡ true
  right-side (inj₁ _) = refl
  right-side (inj₂ (inj₁ _)) = refl
  right-side (inj₂ (inj₂ _)) = refl

  left-edge : ∀ {u v} → (u , v) ∈ map (map-edge T.left) (Network.aliases F)
            → side u ≡ side v
  left-edge member with ∈-map⁻ (map-edge T.left) member
  ... | (u , v) , mem , refl = trans (left-side u) (sym (left-side v))

  right-edge : ∀ {u v} → (u , v) ∈ map (map-edge T.right) (Network.aliases G)
             → side u ≡ side v
  right-edge member with ∈-map⁻ (map-edge T.right) member
  ... | (u , v) , mem , refl = trans (right-side u) (sym (right-side v))

  connected-side : ∀ {u v} → W.Connected u v → side u ≡ side v
  connected-side W.same = refl
  connected-side (W.alias member) = [ left-edge , right-edge ]′
    (∈-++⁻ (map (map-edge T.left) (Network.aliases F)) member)
  connected-side (W.reverse p) = sym (connected-side p)
  connected-side (W.join p q) = trans (connected-side p) (connected-side q)

  false≢true : false ≢ true
  false≢true ()

  no-cross-synchronization : ∀ u v → ¬ (W.Connected (T.left u) (T.right v))
  no-cross-synchronization u v conn = false≢true
    (trans (sym (left-side u)) (trans (connected-side conn) (right-side v)))

  no-cross-participants : ∀ {n x q q′ k p j r} (gather : E.Gather n x q q′)
    → E.Gather.selected gather (inj₁ k) ≡ just p
    → E.Gather.selected gather (inj₂ j) ≡ just r → ⊥
  no-cross-participants {k = k} {p = p} {j = j} {r = r} gather left right =
    no-cross-synchronization (Network.local-wire F (k , p)) (Network.local-wire G (j , r))
      (W.join (E.Gather.on-wire gather {k = inj₁ k} {p = p} left)
        (W.reverse (E.Gather.on-wire gather {k = inj₂ j} {p = r} right)))
