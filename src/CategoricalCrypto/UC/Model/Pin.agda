{-# OPTIONS --safe --without-K --guardedness #-}

-- The inherited metatheory, exercised at the model.  Nothing is proved here —
-- every right-hand side is a name from `Abstract2` — which is the point of the
-- ruled direction: `_≈ᵁ_`, `_≤UC_`, `≤UC-refl`, `dummy-complete`, `≤UC-trans`,
-- `UC-compose` and `≈ᵁ⇒≈ℰ` come with the setup.
--
-- The module exists to PRICE those application sites, because they are what the
-- seal was measured against: this is the same six-statement text that costs
-- 158.8 s at a transparent machine index and OOMs at 12 GiB at a transparent
-- `𝒢` (`spike-stduc-perf`, `Spike.agda`'s table).  Sealed it is at the startup
-- floor, so the applications need neither eta-expansion nor pinned implicits —
-- the two cures that are all one gets without a seal.

open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (Σ-syntax)
open import Data.Sum.Base using (inj₁; inj₂)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (wireᴹ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Model.Pin where

private variable A B C X Y P Q : Channel

------------------------------------------------------------------------
-- The bare kernel `≈ℰ`, including between machine COMPOSITES

≈ℰ-app : {f g : A ⇒ B} → f ≈ℰ g → f ≈ℰ g
≈ℰ-app e = e

≈ℰ-comp-trans : {f : A ⇒ B} {g : B ⇒ C} {h k : A ⇒ C}
              → g ∘ f ≈ℰ h → h ≈ℰ k → g ∘ f ≈ℰ k
≈ℰ-comp-trans = ≈ℰ-trans

------------------------------------------------------------------------
-- The U-kernel `≈ᵁ` and the UC order

≈ᵁ-app : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ᵁ g
≈ᵁ-app e = e

≈ᵁ-comp-app : {f : A ⇒ T₀ X B} {h : B ⇒ T₀ P C} {k : A ⇒ T₀ (X ⊗₀ P) C}
            → h ∙ f ≈ᵁ k → h ∙ f ≈ᵁ k
≈ᵁ-comp-app e = e

≤UC-app : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UC g → f ≤UC g
≤UC-app p = p

------------------------------------------------------------------------
-- The metatheorems, applied at homs of the seal

refl-at : (f : A ⇒ T₀ X B) → f ≤UC f
refl-at = ≤UC-refl

dummy-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
         → Σ[ s₀ ∈ Y ⇒ X ] f ≈ᵁ sub s₀ ∘ g → f ≤UC g
dummy-at = dummy-complete

trans-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} {h : A ⇒ T₀ P B}
         → f ≤UC g → g ≤UC h → f ≤UC h
trans-at = ≤UC-trans

compose-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
             {h : B ⇒ T₀ P C} {k : B ⇒ T₀ Q C}
           → f ≤UC g → h ≤UC k → h ∙ f ≤UC k ∙ g
compose-at = UC-compose

collapse-at : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰ g
collapse-at = ≈ᵁ⇒≈ℰ

------------------------------------------------------------------------
-- …and at a CONCRETE machine process

-- The stateless relay that exposes its own caller interface as its adversary
-- grade, so `relayᵒ A` is a graded hom whose grade is real data.  `gradedᵒ` is
-- what makes it nameable: the seal hides `_⊗₀_`, so `T₀ X B` cannot be met by a
-- machine on the interface sum without a coercion out of the `opaque` block.
relayᵒ : (A : Iface) → ifaceᵒ A ⇒ T₀ (ifaceᵒ A) (ifaceᵒ unitᴵ)
relayᵒ A = gradedᵒ (wireᴹ inj₁ down)
  where
  down : Neg (A ⊗ᴵ unitᴵ) → Neg A
  down (inj₁ n) = n
  down (inj₂ e) = ⊥-elim e

relay-emulates : (A : Iface) → relayᵒ A ≤UC relayᵒ A
relay-emulates A = ≤UC-refl (relayᵒ A)

relay-compose : (A : Iface)
              → relayᵒ unitᴵ ∙ relayᵒ A ≤UC relayᵒ unitᴵ ∙ relayᵒ A
relay-compose A = UC-compose (relay-emulates A) (relay-emulates unitᴵ)
