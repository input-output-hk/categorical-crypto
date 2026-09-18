{-# OPTIONS --safe --without-K --guardedness #-}

-- What the model adds to the identification it already has.  `UC.Model.Setup`
-- IS `UC.Core.Bridge` at the seal, so `_≈ℰᶜ_` and its two-way agreement with
-- `_≈ᵁ_` arrive with the setup; here is what only the model has.
--
-- The vocabulary is the trap, and this is the one place it is spelled out.  The
-- core's `_≈ℰ_` (`UC.Environment`) quantifies over an ancilla; StdUC's `_≈ℰ_`
-- is the bare presheaf kernel and does not.  So the two relations sharing that
-- name are NOT the same one: what the core's coincides with is StdUC's `_≈ᵁ_`.
-- Coming back from the BARE kernel would be `Abstract2.bridge`, which wants
-- `GradeStable` for `ℰᵒ`; this model does not supply it — the core buys grade
-- stability by putting the ancilla into the relation instead
-- (`UC.Environment.grade-stable`).
--
-- At UNGRADED homs `_≈ᵁ_` says nothing — it is stated at `A ⇒ T₀ X B` — while
-- the core's relation is stated at every codomain.  `_≈ᴳ_` below is what it is
-- there, and agrees with `_≈ᵁ_` wherever the latter is stated, so the seam can
-- be read in one vocabulary.
--
-- Universal composition is what the two orders agreeing RETIRES: `UC.Emulation`
-- could only state it, and `≤UCᶜ⇔≤UC` carries `Abstract2.UC-compose` — already
-- a theorem — across, leaving the core nothing to owe.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗; μ-α⇐)
import Categories.Morphism.Reasoning as MR

open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ; suc)

open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Model.Bridge where

open HomReasoning
open MR ∣machines∣ using (cancelˡ)

private variable A B C X Y : Channel

module E = Em baseᵗ

------------------------------------------------------------------------
-- The same identification at ungraded homs

infix 4 _≈ᴳ_

-- The bare kernel read at every ancilla: the largest grade-stable relation
-- under `_≈ℰ_`, and the inherited spelling of the core's relation where
-- `_≈ᵁ_` is not stated.
_≈ᴳ_ : (f g : A ⇒ B) → Set (suc 0ℓ)
_≈ᴳ_ f g = (Y : Channel) → T₁ Y f ≈ℰ T₁ Y g

≈ᴳ-refl : {f : A ⇒ B} → f ≈ᴳ f
≈ᴳ-refl _ = ≈ℰ-refl

≈ᴳ-sym : {f g : A ⇒ B} → f ≈ᴳ g → g ≈ᴳ f
≈ᴳ-sym h Y = ≈ℰ-sym (h Y)

≈ᴳ-trans : {f g h : A ⇒ B} → f ≈ᴳ g → g ≈ᴳ h → f ≈ᴳ h
≈ᴳ-trans p q Y = ≈ℰ-trans (p Y) (q Y)

≈C⇒≈ᴳ : {f g : A ⇒ B} → f ≈ g → f ≈ᴳ g
≈C⇒≈ᴳ e _ = ≈C⇒≈ℰ (T-resp-≈ e)

≈ᴳ-congˡ : (k : B ⇒ C) {f g : A ⇒ B} → f ≈ᴳ g → k ∘ f ≈ᴳ k ∘ g
≈ᴳ-congˡ k h Y = ≈ℰ-trans (≈C⇒≈ℰ T-homomorphism)
  (≈ℰ-trans (≈ℰ-cong-post (T₁ Y k) (h Y)) (≈C⇒≈ℰ (⟺ T-homomorphism)))

≈ᴳ-congʳ : (l : C ⇒ A) {f g : A ⇒ B} → f ≈ᴳ g → f ∘ l ≈ᴳ g ∘ l
≈ᴳ-congʳ l h Y = ≈ℰ-trans (≈C⇒≈ℰ T-homomorphism)
  (≈ℰ-trans (≈ℰ-cong-pre (T₁ Y l) (h Y)) (≈C⇒≈ℰ (⟺ T-homomorphism)))

-- Where `_≈ᵁ_` is stated the two coincide: the prefix `μ Y X` it carries is an
-- iso (`μ-α⇐`, `associator.isoʳ`), so composing with it changes nothing.
≈ᴳ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ᴳ g → f ≈ᵁ g
≈ᴳ⇒≈ᵁ {X = X} h Y = ≈ℰ-cong-post (μ Y X) (h Y)

≈ᵁ⇒≈ᴳ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ᴳ g
≈ᵁ⇒≈ᴳ {X = X} {f = f} {g} u Y =
  ≈ℰ-trans (≈C⇒≈ℰ (⟺ (cancel f))) (≈ℰ-trans (≈ℰ-cong-post α⇒ (u Y)) (≈C⇒≈ℰ (cancel g)))
  where
  cancel : {A′ B′ : Channel} (x : A′ ⇒ T₀ X B′) → α⇒ ∘ μ Y X ∘ T₁ Y x ≈ T₁ Y x
  cancel _ = cancelˡ (∘-resp-≈ʳ (μ-α⇐ 𝔾ᵒ Y X) ○ associator.isoʳ)

-- …and everywhere it is the core's, which is what licenses reading a seam
-- statement in the inherited vocabulary without weakening it.
private
  -- The core's action is the tensor's own `F₁`; the triple derives its `T₁` and
  -- pays one triangle for the identification.
  reT₁ : {Y : Channel} (f : A ⇒ B) (e : Test (Y ⊗₀ B)) (m : Closure (Y ⊗₀ A))
       → (e ∘ T₁ Y f) ∘ m ≈ (e ∘ E.T₁ Y f) ∘ m
  reT₁ {Y = Y} f _ _ = (refl⟩∘⟨ T₁-⊗ 𝔾ᵒ Y f) ⟩∘⟨refl

≈ᴳ⇒≈ℰᶜ : {f g : A ⇒ B} → f ≈ᴳ g → f ≈ℰᶜ g
≈ᴳ⇒≈ℰᶜ {f = f} {g} h Y e m =
  ∼ᴼ-resp (obs-resp (reT₁ f e m)) (obs-resp (reT₁ g e m)) (KE.run∼ (h Y) {e} m)

≈ℰᶜ⇒≈ᴳ : {f g : A ⇒ B} → f ≈ℰᶜ g → f ≈ᴳ g
≈ℰᶜ⇒≈ᴳ {f = f} {g} h Y = KE.mk∼ λ {e} m →
  ∼ᴼ-resp (obs-resp (⟺ (reT₁ f e m))) (obs-resp (⟺ (reT₁ g e m))) (h Y e m)

≈ᴳ⇔≈ℰᶜ : {f g : A ⇒ B} → f ≈ᴳ g ⇔ f ≈ℰᶜ g
≈ᴳ⇔≈ℰᶜ {f = f} {g} = mk⇔ {B = f ≈ℰᶜ g} ≈ᴳ⇒≈ℰᶜ ≈ℰᶜ⇒≈ᴳ

------------------------------------------------------------------------
-- …and the two emulation orders agree

infix 4 _≤UCᶜ_

-- Named apart from the inherited `_≤UC_`, whose statement carries the
-- adversary quantifier this one does not.
_≤UCᶜ_ : A ⇒ T₀ X B → A ⇒ T₀ Y B → Set (suc 0ℓ)
_≤UCᶜ_ = E._≤UC_

≤UCᶜ⇒≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g → f ≤UC g
≤UCᶜ⇒≤UC p a = let s , e = E.dummy-complete p a in s , ≈ℰᶜ⇒≈ᵁ e

≤UC⇒≤UCᶜ : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UC g → f ≤UCᶜ g
≤UC⇒≤UCᶜ p = let s , e = ≤UC⇒dummy p in s , ≈ᵁ⇒≈ℰᶜ e

≤UCᶜ⇔≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g ⇔ f ≤UC g
≤UCᶜ⇔≤UC {f = f} {g} = mk⇔ {B = f ≤UC g} ≤UCᶜ⇒≤UC ≤UC⇒≤UCᶜ

------------------------------------------------------------------------
-- The instrument the seam consumes, over the inherited kernel

-- `UC.Environment.≈ℰ-at`: an agreement read at ONE context, presented uniformly
-- in the process.  Stated away from the machine layer for the reason
-- `UC.Seam.Grounding`'s header gives — there a `∼ᴼ` between machine COMPOSITES
-- η-expands the observation record — so the seam supplies the three components
-- and the equation, and nothing else.
≈ᴳ-at : (Y : Channel) (Et : Test (Y ⊗₀ B)) (m : Closure (Y ⊗₀ A))
        (k : A ⇒ B → Closure Ωᵒ) → ((w : A ⇒ B) → (Et ∘ T₁ Y w) ∘ m ≈ k w)
      → {f g : A ⇒ B} → f ≈ᴳ g → Obs (k f) ∼ᴼ Obs (k g)
≈ᴳ-at Y Et m k eq {f} {g} r =
  ∼ᴼ-resp (obs-resp (eq f)) (obs-resp (eq g)) (KE.run∼ (r Y) {Et} m)
