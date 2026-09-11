{-# OPTIONS --safe --without-K --guardedness #-}

-- The inherited metatheory, exercised at the model.  Nothing is proved here —
-- every right-hand side is a name from `Abstract2` — which is the point of the
-- ruled direction: `_≈ᵁ_`, `_≤UC_`, `≤UC-refl`, `dummy-complete`, `≤UC-trans`,
-- `UC-compose` and `≈ᵁ⇒≈ℰ` come with the setup.  The five metatheorem sites
-- arrive as `UC.Model.Unit.AnyEnvironment ℰᵒ`, since the statements are
-- ℰ-generic and that module is where they are written.
--
-- The module exists to PRICE those application sites, because they are what the
-- seal was measured against: this is the same six-statement text that costs
-- 158.8 s at a transparent machine index and OOMs at 12 GiB at a transparent
-- `𝒢` (`spike-stduc-perf`, `Spike.agda`'s table).  Sealed it is at the startup
-- floor, so the applications need neither eta-expansion nor pinned implicits —
-- the two cures that are all one gets without a seal.
--
-- What CANNOT be pinned here is behaviour, and the seal is why: `procᵒ` and
-- `unprocᵒ` are `opaque`, so `Obs (procᵒ M) ≡ ⟦ M ⟧ᴼ` is not `refl` for any
-- `M` — measured, the conversion is stuck at the first projection
-- (`Machine.state`'s `obj`), so no budget reaches a value.  `relayᵒ` is out of
-- reach twice over: its codomain carries no verdict either, so `⟦_⟧ᴼ` does not
-- even type-apply and observing it needs a test composed on.  Behaviour is
-- pinned by `refl` one layer down, at the transparent machines
-- (`Protocol.Machine.Pin`); across the seal the same reading is a propositional
-- lemma instead (`UC.Seam.Grounded.plug-run`, over `Seal.unprocᵒ-∘`).

open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (wireᴹ)
open import CategoricalCrypto.UC.Model.Environment using (ℰᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Model.Unit as Unit

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

-- `UC.Model.Unit.AnyEnvironment` states these five over an ARBITRARY
-- environment presheaf, which is what makes the choice of closure object
-- immaterial; instantiating it at `ℰᵒ` is what prices them here, and is the
-- only instance the module has.
open Unit.AnyEnvironment ℰᵒ public

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
