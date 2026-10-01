{-# OPTIONS --safe --without-K #-}

open import Data.List.Base
import Data.List.Membership.Setoid as Membership
open import Data.List.Relation.Binary.Subset.Setoid.Properties
open import Data.List.Relation.Unary.Any as Any
open import Function.Base
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Unary using (Pred)

module Data.List.Relation.Unary.Any.Properties.Ext where

private variable c ℓ p q : Level

module _ (S : Setoid c ℓ) where

  open Setoid S
  open Membership S

  -- `Any-cong` up to a setoid's `_≈_`; stdlib's propositional `Any-cong` needs
  -- set-equality up to `≡`, a stronger premise.
  Any-congˢ : {P : Pred Carrier p} {Q : Pred Carrier q} {σ τ : List Carrier}
            → (∀ {a b} → a ≈ b → P a ⇔ Q b)
            → (∀ {z} → (z ∈ σ) ⇔ (z ∈ τ))
            → Any P σ ⇔ Any Q τ
  Any-congˢ P⇔Q σ≈τ = mk⇔
    (Any-resp-⊆ S Q-resp (λ {z} → Equivalence.to   (σ≈τ {z})) ∘ Any.map to-Q)
    (Any-resp-⊆ S P-resp (λ {z} → Equivalence.from (σ≈τ {z})) ∘ Any.map from-P)
    where
    to-Q = λ {a} → Equivalence.to   (P⇔Q (refl {a}))
    from-P = λ {a} → Equivalence.from (P⇔Q (refl {a}))

    Q-resp = λ {a} {b} (a≈b : a ≈ b) → to-Q ∘ Equivalence.from (P⇔Q (sym a≈b))
    P-resp = λ {a} {b} (a≈b : a ≈ b) → Equivalence.from (P⇔Q (sym a≈b)) ∘ to-Q
