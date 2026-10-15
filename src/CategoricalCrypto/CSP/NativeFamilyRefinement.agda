{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeFamilyRefinement (X B : Set) where

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base

import CategoricalCrypto.CSP.Confinement as Confinement
import CategoricalCrypto.CSP.NativeCorrespondence as Common
import CategoricalCrypto.CSP.NativeRefinement as Native

module C = Common X B
module N = Native (⊤ × X) B (λ _ → true)
open C using (Nonempty; one; _∙_; Family; fold)
open C.L
open N.R
module F = Confinement (⊤ × X) C.O.Index ⊤
module S = N.Separated (λ _ → ⊤) (λ _ → ⊤) (λ e ())

unrestricted : ∀ p → F.OffersOnly (λ _ → ⊤) p
F.OffersOnly.now (unrestricted p) step = tt
F.OffersOnly.after (unrestricted p) {q = q} step = unrestricted q

parallel : ∀ {p q p′ q′} → p ⊑ p′ → q ⊑ q′ → C.O.Par p q ⊑ C.O.Par p′ q′
parallel rp rq = S.par-refines rp rq (unrestricted _) (unrestricted _) (unrestricted _) (unrestricted _)

family : ∀ s {p q : Family s} → (∀ k → p k ⊑ q k) → fold s p ⊑ fold s q
family one pointwise = pointwise tt
family (s ∙ t) pointwise = parallel (family s (λ k → pointwise (inj₁ k))) (family t (λ k → pointwise (inj₂ k)))

hidden-family : ∀ s {p q : Family s} → (∀ k → p k ⊑ q k)
  → C.O.Hide (λ _ → true) (fold s p) ⊑ C.O.Hide (λ _ → true) (fold s q)
hidden-family s pointwise = N.hide-refines (λ _ → true) (family s pointwise)
