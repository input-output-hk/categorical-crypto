{-# OPTIONS --safe --without-K #-}

-- The distributional hom equality on protocols (`docs/uc-setup-ssp-dist.md`
-- §1): `P ≈ᵈ P′` when every padding `(Y ⊗ P) ⊗ Z`, read by every
-- distinguisher against every game, shows the same verdict distribution —
-- `Standard2.UKernel`'s two-sided ancilla kernel of `ℰᵖ`, a monoidal
-- congruence by construction.  The ancillas let the distinguisher and the
-- game share oracles, which is what a tensor needs.  Sampling simulations
-- prove it (`⊑⇒≈ᵈ`): their squares are per activation, against every oracle.

module CategoricalCrypto.SSP.Dist where

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor

open import Level
open import Relation.Binary.Structures

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.SSP.Dist.Kernel
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.SSP.Setup

import CategoricalCrypto.Standard2.UKernel as UKernel

private
  module K = UKernel Protᴹ ℰᵖ
  module U = MonoidalCongruence K.uKernel
  variable A B X : Iface

infix 4 _≈ᵈ_
record _≈ᵈ_ (P P′ : Protocol A B) : Set₁ where
  constructor mk≈ᵈ
  field run≈ᵈ : P K.∼ P′
open _≈ᵈ_ public

≈ᵈ-isEquivalence : IsEquivalence (_≈ᵈ_ {A} {B})
≈ᵈ-isEquivalence {A} {B} = record
  { refl  = λ {P} → mk≈ᵈ (∼.refl {P})
  ; sym   = λ {P} {P′} e → mk≈ᵈ (∼.sym {P} {P′} (run≈ᵈ e))
  ; trans = λ {P} {P′} {P″} e e′ → mk≈ᵈ (∼.trans {P} {P′} {P″} (run≈ᵈ e) (run≈ᵈ e′)) }
  where module ∼ = IsEquivalence (K.∼-equiv {A} {B})

module ≈ᵈ {A B} = IsEquivalence (≈ᵈ-isEquivalence {A} {B})

≈ᵖ⇒≈ᵈ : {P P′ : Protocol A B} → P ≈ᵖ P′ → P ≈ᵈ P′
≈ᵖ⇒≈ᵈ {P = P} {P′} e = mk≈ᵈ (U.≈⇒∼ {f = P} {g = P′} e)

congᵈ : MonoidalCongruence Protᴹ (suc 0ℓ)
congᵈ = record
  { _∼_ = _≈ᵈ_ ; ∼-equiv = ≈ᵈ-isEquivalence ; ≈⇒∼ = ≈ᵖ⇒≈ᵈ
  ; ∘-resp-∼ = λ {_} {_} {_} {f} {h} {g} {i} e e′ →
      mk≈ᵈ (U.∘-resp-∼ {f = f} {h = h} {g = g} {i = i} (run≈ᵈ e) (run≈ᵈ e′))
  ; ⊗-resp-∼ = λ {_} {_} {_} {_} {f} {h} {g} {i} e e′ →
      mk≈ᵈ (U.⊗-resp-∼ {f = f} {h = h} {g = g} {i = i} (run≈ᵈ e) (run≈ᵈ e′)) }

≈ᵈ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ᵈ g → f ≈ᵁ g
≈ᵈ⇒≈ᵁ {f = f} {g} e = K.∼⇒≈ᵁ {f = f} {g = g} (run≈ᵈ e)

≈ᵈ⇒≋ : {P P′ : Protocol A B} → P ≈ᵈ P′ → Setoids (suc 0ℓ) (suc 0ℓ) [ Functor.₁ ℰᵖ P ≈ Functor.₁ ℰᵖ P′ ]
≈ᵈ⇒≋ {P = P} {P′} e {t} = KE.run∼ (K.∼⇒≈ℰ {f = P} {g = P′} (run≈ᵈ e)) {t}

⊑⇒≈ᵈ : {P P′ : Protocol A B} → P ⊑ P′ → P ≈ᵈ P′
⊑⇒≈ᵈ {P = P} {P′} e = mk≈ᵈ λ Y Z → KE.mk∼ λ {t} m →
  zero⇒positive {runᵖ ((t ∘ᵖ (wireᵖ {Y} ⊗ᵖ P) ⊗ᵖ wireᵖ {Z}) ∘ᵖ m)} {runᵖ ((t ∘ᵖ (wireᵖ {Y} ⊗ᵖ P′) ⊗ᵖ wireᵖ {Z}) ∘ᵖ m)}
    (≈Mℚ⇒≈[0] {runᵖ ((t ∘ᵖ (wireᵖ {Y} ⊗ᵖ P) ⊗ᵖ wireᵖ {Z}) ∘ᵖ m)} {runᵖ ((t ∘ᵖ (wireᵖ {Y} ⊗ᵖ P′) ⊗ᵖ wireᵖ {Z}) ∘ᵖ m)}
              (⊑-run (⊑-⊗ˡ (wireᵖ {Z}) (⊑-⊗ʳ (wireᵖ {Y}) e)) t m))
  where open AllPositive ℚ-refinement Approximation⊥
