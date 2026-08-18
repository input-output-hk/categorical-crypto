{-# OPTIONS --safe --without-K #-}

open import Data.List.Base using (List)
import Data.List.Membership.Setoid as Membership
open import Data.List.Relation.Binary.Subset.Setoid.Properties using (Any-resp-⊆)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Unary using (Pred)

module Data.List.Relation.Unary.Any.Properties.Ext where

private variable c ℓ p q : Level

module _ (S : Setoid c ℓ) where

  open Setoid S using (Carrier; _≈_; refl; sym)
  open Membership S using (_∈_)

  -- `Any-cong` over a setoid: the two predicates need only agree on `_≈_`-related
  -- points, and the two lists need only be set-equal up to `_≈_`.  Its
  -- propositional counterpart takes a stronger second premise, so it does not
  -- apply.  Both `Respects` proofs come out of the first premise: read at
  -- reflexivity it turns `P` into `Q`, and read at `sym` it turns `Q` back.
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
