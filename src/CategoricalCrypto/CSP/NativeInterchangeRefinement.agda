{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeInterchangeRefinement (X B : Set) where

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.CSP.NativeInterchange as Interchange
import CategoricalCrypto.CSP.NativeRefinement as Native

module I = Interchange X B
module A = Native (Bool × X) B (λ _ → true)
module P = Native (Bool × X) B (λ _ → false)
open I.L
open A.R
open I.Quad

module Separated = P.Separated (λ e → proj₁ e ≡ false) (λ e → proj₁ e ≡ true) (λ e _ → I.apart e)
module Shared = A.Separated (λ _ → ⊤) (λ _ → ⊤) (λ e ())

unrestricted : ∀ p → I.C.OffersOnly (λ _ → ⊤) p
I.C.OffersOnly.now (unrestricted p) step = tt
I.C.OffersOnly.after (unrestricted p) {q = q} step = unrestricted q

shared : ∀ {p q p′ q′} → p ⊑ p′ → q ⊑ q′ → I.A.Par p q ⊑ I.A.Par p′ q′
shared rp rq = Shared.par-refines rp rq (unrestricted _) (unrestricted _) (unrestricted _) (unrestricted _)

strong-symmetric : ∀ {p q} → I.Strong p q → I.Strong q p
I.Strong.forward (strong-symmetric proof) step = continue (I.Strong.backward proof step)
  where
  continue : ∀ {q l t} → Σ Tree (λ p → q ─[ l ]→ p × I.Strong p t)
    → Σ Tree (λ p → q ─[ l ]→ p × I.Strong t p)
  continue (p , move , next) = p , move , strong-symmetric next
I.Strong.backward (strong-symmetric proof) step = continue (I.Strong.forward proof step)
  where
  continue : ∀ {p l t} → Σ Tree (λ q → p ─[ l ]→ q × I.Strong t q)
    → Σ Tree (λ q → p ─[ l ]→ q × I.Strong q t)
  continue (q , move , next) = q , move , strong-symmetric next

strong-refines : ∀ {p q} → I.Strong p q → p ⊑ q
_⊑_.match (strong-refines proof) step = continue (I.Strong.backward proof step)
  where
  continue : ∀ {p l t} → Σ Tree (λ s → p ─[ l ]→ s × I.Strong s t)
    → Σ Tree (λ s → p ─[ l ]→ s × s ⊑ t)
  continue (s , move , next) = s , move , strong-refines next
_⊑_.ready (strong-refines proof) (t , step) =
  let s , move , _ = I.Strong.forward proof step in s , move

left-refines : ∀ {f g} → p₁ f ⊑ p₁ g → p₂ f ⊑ p₂ g → q₁ f ⊑ q₁ g → q₂ f ⊑ q₂ g
  → I.left-source f ⊑ I.left-source g
left-refines {f} {g} rp₁ rp₂ rq₁ rq₂ = shared
  (Separated.par-refines rp₁ rp₂ (cp₁ f) (cp₂ f) (cp₁ g) (cp₂ g))
  (Separated.par-refines rq₁ rq₂ (cq₁ f) (cq₂ f) (cq₁ g) (cq₂ g))

right-refines : ∀ {f g} → p₁ f ⊑ p₁ g → p₂ f ⊑ p₂ g → q₁ f ⊑ q₁ g → q₂ f ⊑ q₂ g
  → I.right-source f ⊑ I.right-source g
right-refines {f} {g} rp₁ rp₂ rq₁ rq₂ = transitive (strong-refines (strong-symmetric (I.interchange f)))
  (transitive (left-refines {f} {g} rp₁ rp₂ rq₁ rq₂) (strong-refines (I.interchange g)))

hidden-link-refines : ∀ {f g} → p₁ f ⊑ p₁ g → p₂ f ⊑ p₂ g → q₁ f ⊑ q₁ g → q₂ f ⊑ q₂ g
  → I.A.Hide (λ _ → true) (I.left-source f) ⊑ I.A.Hide (λ _ → true) (I.right-source g)
hidden-link-refines {f} {g} rp₁ rp₂ rq₁ rq₂ = transitive
  (A.hide-refines (λ _ → true) (left-refines {f} {g} rp₁ rp₂ rq₁ rq₂))
  (strong-refines (I.hidden-interchange g))

hidden-link-agreement : ∀ f → RawAgreement
  (I.A.Hide (λ _ → true) (I.left-source f)) (I.A.Hide (λ _ → true) (I.right-source f))
hidden-link-agreement f = mutual-agreement (strong-refines (I.hidden-interchange f))
  (strong-refines (strong-symmetric (I.hidden-interchange f)))
