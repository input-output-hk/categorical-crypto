{-# OPTIONS --safe --without-K #-}

-- The core's environment agreement IS the inherited `_≈ᵁ_`, at any monoidal
-- base and observation — hence the inherited order, hence
-- `Abstract2.UC-compose` on anything the core proves.
--
-- The two directions spend different things.  Forward needs no rebracketing
-- and is what an ingested bound spends:
--
--     f ≈ℰᶜ g  ─grade-stable→  T₁ Y f ≈ℰᶜ T₁ Y g  ─congˡ→
--     μ Y X ∘ T₁ Y f ≈ℰᶜ μ Y X ∘ T₁ Y g  ─at the unit ancilla→  …≈ℰ…
--
-- `grade-stable` is `UC.Environment`'s theorem — the ancilla quantifier
-- absorbing a bypass wire, with no hypothesis under it — which is exactly what
-- `Abstract2.bridge` asks for and cannot get from a BARE kernel (`GradeStable`
-- for `ℰᴼ` is not available; `UC.Model.Bridge`'s header records that).  The
-- last step is the unit ancilla, where the two wires cancel by the unitor's
-- naturality and its own iso, and the trivial-grade relay is the tensor with an
-- identity on the nose (`gradingᵗ`), so nothing needs `T₁-⊗` there.
--
-- Back, the prefix `μ Y X ∘ T₁ Y f` that `_≈ᵁ_` carries is `α⇐ ∘ id ⊗₁ f`
-- (`μT₁-α⇐`), so cancelling it against `α⇒` in the test reads the hypothesis
-- at `Y` as the core's experiment at that ancilla.  That cancellation is
-- `shuffle⇒`/`shuffle⇐`, which the model's robustness and quantitative layers
-- consume directly.
--
-- Everything is generic: the whole argument is monoidal laws plus the core's
-- own congruences, so no instance unfolds while it is checked.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗; μT₁-α⇐)
import Categories.Morphism.Reasoning as MR

open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Core using (Observation; UCBase)

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Environment as Env

module CategoricalCrypto.UC.Core.Bridge
  {o ℓ e os ℓs : Level} (M : MonoidalCategory o ℓ e)
  (O : Observation (MonoidalCategory.U M) os ℓs) where

-- The core's base at the standard grading: what `UC.Family` is built over, one
-- instantiation up.
baseᵗ : UCBase o ℓ e os ℓs
baseᵗ = record { 𝒞 = MonoidalCategory.U M ; grading = Std.gradingᵗ M ; observation = O }

module C = Env baseᵗ

open Std2.StdUC M C.ℰᴼ public

open HomReasoning
open MR ∣machines∣ using (cancelInner)

infix 4 _≈ℰᶜ_

-- Named apart from the inherited `_≈ℰ_`, which is the BARE presheaf kernel and
-- has no ancilla in it (`UC.Model.Bridge`'s header).
_≈ℰᶜ_ : {A B : Channel} (f g : A ⇒ B) → Set (o ⊔ ℓ ⊔ ℓs)
_≈ℰᶜ_ = C._≈ℰ_

private
  -- The unit ancilla, plugged: `T₁ unit u` is `id ⊗₁ u` at this grading, and
  -- the two unitor wires cancel around it.
  plug : {A B : Channel} (t : B ⇒ C.Ω) (u : A ⇒ B) (m : C.𝟙 ⇒ A)
       → ((t ∘ unitorˡ.from) ∘ C.T₁ unit u) ∘ (unitorˡ.to ∘ m) ≈ (t ∘ u) ∘ m
  plug t u m = ((assoc ○ (refl⟩∘⟨ unitorˡ-commute-from) ○ sym-assoc) ⟩∘⟨refl)
             ○ cancelInner unitorˡ.isoʳ

-- The core's relation refines the bare kernel: an agreement seen by every
-- ancilla is in particular seen by the trivial one.
≈ℰᶜ⇒≈ℰ : {A B : Channel} {f g : A ⇒ B} → f ≈ℰᶜ g → f ≈ℰ g
≈ℰᶜ⇒≈ℰ {f = f} {g} h = KE.mk∼ λ {t} m →
  C.∼-cast (plug t f m) (plug t g m) (h unit (t ∘ unitorˡ.from) (unitorˡ.to ∘ m))

≈ℰᶜ⇒≈ᵁ : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≈ᵁ g
≈ℰᶜ⇒≈ᵁ {f = f} {g} h Y =
  ≈ℰ-trans (≈C⇒≈ℰ (step f))
           (≈ℰ-trans (≈ℰᶜ⇒≈ℰ (C.≈ℰ-congˡ (μ Y _) (C.grade-stable Y h)))
                     (≈ℰ-sym (≈C⇒≈ℰ (step g))))
  where
  step : {A B X : Channel} (u : A ⇒ T₀ X B) → μ Y X ∘ T₁ Y u ≈ μ Y X ∘ id ⊗₁ u
  step u = refl⟩∘⟨ T₁-⊗ M Y u

-- The cancellation the backward direction is, in the two orientations its
-- consumers state their own bracketing at.
shuffle⇒ : {A B X Y : Channel} (f : A ⇒ T₀ X B) (e : C.Test (Y ⊗₀ X ⊗₀ B))
           (m : C.Closure (Y ⊗₀ A))
         → ((e ∘ α⇒) ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ e ∘ id ⊗₁ f ∘ m
shuffle⇒ {Y = Y} f e m =
  ((refl⟩∘⟨ μT₁-α⇐ M Y f) ⟩∘⟨refl) ○ (cancelInner associator.isoʳ ⟩∘⟨refl) ○ assoc

shuffle⇐ : {A B X Y : Channel} (f : A ⇒ T₀ X B) (e : C.Test ((Y ⊗₀ X) ⊗₀ B))
           (m : C.Closure (Y ⊗₀ A))
         → (e ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ (e ∘ α⇐) ∘ id ⊗₁ f ∘ m
shuffle⇐ {Y = Y} f e m =
  ((refl⟩∘⟨ μT₁-α⇐ M Y f) ⟩∘⟨refl) ○ (sym-assoc ⟩∘⟨refl) ○ assoc

≈ᵁ⇒≈ℰᶜ : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰᶜ g
≈ᵁ⇒≈ℰᶜ {A} {B} {X} {f} {g} u Y E m = C.∼-cast (step f) (step g) (KE.run∼ (u Y) {E ∘ α⇒} m)
  where
  step : (x : A ⇒ T₀ X B) → ((E ∘ α⇒) ∘ (μ Y X ∘ T₁ Y x)) ∘ m ≈ (E ∘ C.T₁ Y x) ∘ m
  step x = shuffle⇒ x E m ○ sym-assoc

≈ℰᶜ⇔≈ᵁ : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g ⇔ f ≈ᵁ g
≈ℰᶜ⇔≈ᵁ = mk⇔ ≈ℰᶜ⇒≈ᵁ ≈ᵁ⇒≈ℰᶜ

-- …and the inherited order, at the identity dummy.  This is what
-- `UC-compose`, `≤UC-trans` and `dummy-complete` are stated over, so a bound
-- the core proves enters the metatheory here.
≈ℰᶜ⇒≤UC : {A B X : Channel} {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≤UC g
≈ℰᶜ⇒≤UC {g = g} h =
  dummy-complete (id , ≈ᵁ-trans (≈ℰᶜ⇒≈ᵁ h) (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ g))))
