{-# OPTIONS --safe --without-K --guardedness #-}

-- Where the hand-rolled qualitative core meets the inherited metatheory: the
-- machine model carries BOTH, and this module identifies them.
--
-- The identification is exact in both directions, and its shape is a warning
-- about the vocabulary.  The core's `_≈ℰ_` (`UC.Environment`) quantifies over an
-- ancilla; StdUC's `_≈ℰ_` is the bare presheaf kernel and does not.  So the two
-- relations that share the name are NOT the same one — what the core's `_≈ℰ_`
-- coincides with is StdUC's `_≈ᵁ_`, through the operational reading
-- `UC.Model.Reading._≈ᴬ_`, which differs from it by one `assoc` and nothing
-- else.  The core's `_≤UC_` then coincides with StdUC's, both ways: the core's
-- `dummy-complete` supplies the universal quantification StdUC's order carries
-- in its statement, and the core's `≤UC⁺⇒≤UC` takes it back.
--
-- The core's one OPEN metatheorem is discharged as a corollary: `UC-compose` is
-- a `Set` in `UC.Emulation` because the chain needs a `sub`/`T₁` interchange
-- and `a⇒`-naturality that `Grading` does not ask for.  At the model the graded
-- composite `_⊙_` IS the Kleisli one — `ext X h` is `α⇐ ∘ id ⊗₁ h` on the nose
-- (`CurriedTensor.Properties.ext-⊗`) — so `_⊙_` and `_∙_` differ by one
-- re-bracketing and the inherited theorem transports.
--
-- Nothing here unfolds the seal: the core's `UCBase` is assembled from
-- `UC.Core.Standard.gradingᵗ` at `𝔾ᵒ` and `UC.Model.Observation`, both of which
-- name the sealed bundle without opening it.

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ; suc)

open import ProbabilisticLogic.Dp using (Dₚ)

open import CategoricalCrypto.UC.Core using (Observation; UCBase)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Reading using (_≈ᴬ_; ≈ᵁ⇒≈ᴬ; ≈ᴬ⇒≈ᵁ)
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣; 𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Model.Bridge where

open HomReasoning

private variable A B C X Y P : Channel

------------------------------------------------------------------------
-- The core's `UCBase` at the model

-- The core asks for strictly less than `UCSetup` does: an action of grades and
-- a closed run.  Both are already here — the action is the one a monoidal
-- category carries for free, and the run is the model's own observation.
observationᵒ : Observation ∣𝔾ᵒ∣ 0ℓ 0ℓ
observationᵒ = record
  { 𝟙 = 𝟘ᵒ ; Ω = Ωᵒ ; Obs = Dₚ Bool ; ⟦_⟧ = Obs
  ; _∼_ = _∼ᴼ_ ; ∼-isEquivalence = ∼ᴼ-isEquivalence
  ; ⟦⟧-resp-≈ = λ e → ≈ₚ⇒∼ᴼ (obs-resp e)
  }

ucBaseᵒ : UCBase (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ
ucBaseᵒ = record
  { 𝒞 = ∣𝔾ᵒ∣ ; grading = Std.gradingᵗ 𝔾ᵒ ; observation = observationᵒ }

module E = Em ucBaseᵒ

infix 4 _≈ℰᶜ_ _≤UCᶜ_

-- The core's two relations, at the model.  Named apart from the inherited
-- `_≈ℰ_`/`_≤UC_` because the first pair genuinely differs from the second.
_≈ℰᶜ_ : (f g : A ⇒ B) → Set (suc 0ℓ)
_≈ℰᶜ_ = E._≈ℰ_

_≤UCᶜ_ : A ⇒ T₀ X B → A ⇒ T₀ Y B → Set (suc 0ℓ)
_≤UCᶜ_ = E._≤UC_

------------------------------------------------------------------------
-- The core's `_≈ℰ_` is the inherited `_≈ᵁ_`

-- One `assoc`: the core reads a context as `(E ∘ T₁ Y f) ∘ m`, the operational
-- reading as `E ∘ id ⊗₁ f ∘ m`.
≈ℰᶜ⇒≈ᴬ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≈ᴬ g
≈ℰᶜ⇒≈ᴬ h Y e m = ∼ᴼ-resp (obs-resp assoc) (obs-resp assoc) (h Y e m)

≈ᴬ⇒≈ℰᶜ : {f g : A ⇒ T₀ X B} → f ≈ᴬ g → f ≈ℰᶜ g
≈ᴬ⇒≈ℰᶜ h Y e m = ∼ᴼ-resp (obs-resp sym-assoc) (obs-resp sym-assoc) (h Y e m)

≈ℰᶜ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≈ᵁ g
≈ℰᶜ⇒≈ᵁ h = ≈ᴬ⇒≈ᵁ (≈ℰᶜ⇒≈ᴬ h)

≈ᵁ⇒≈ℰᶜ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰᶜ g
≈ᵁ⇒≈ℰᶜ u = ≈ᴬ⇒≈ℰᶜ (≈ᵁ⇒≈ᴬ u)

≈ℰᶜ⇔≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g ⇔ f ≈ᵁ g
≈ℰᶜ⇔≈ᵁ {f = f} {g} = mk⇔ {B = f ≈ᵁ g} ≈ℰᶜ⇒≈ᵁ ≈ᵁ⇒≈ℰᶜ

-- …hence strictly finer than the inherited bare kernel, which has no ancilla in
-- it.  The converse is `Abstract2.bridge` and wants `GradeStable`, which this
-- model does not supply: the core buys grade stability by putting the ancilla
-- into the relation instead (`UC.Environment.grade-stable`).
≈ℰᶜ⇒≈ℰ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≈ℰ g
≈ℰᶜ⇒≈ℰ h = ≈ᵁ⇒≈ℰ (≈ℰᶜ⇒≈ᵁ h)

------------------------------------------------------------------------
-- …and the two emulation orders agree

≤UCᶜ⇒≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g → f ≤UC g
≤UCᶜ⇒≤UC p a = let s , e = E.dummy-complete p a in s , ≈ℰᶜ⇒≈ᵁ e

≤UC⇒≤UCᶜ : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UC g → f ≤UCᶜ g
≤UC⇒≤UCᶜ p = E.≤UC⁺⇒≤UC λ a → let s , e = p a in s , ≈ᵁ⇒≈ℰᶜ e

≤UCᶜ⇔≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g ⇔ f ≤UC g
≤UCᶜ⇔≤UC {f = f} {g} = mk⇔ {B = f ≤UC g} ≤UCᶜ⇒≤UC ≤UC⇒≤UCᶜ

------------------------------------------------------------------------
-- The core's open metatheorem, discharged

⊙-∙ : (h : B ⇒ T₀ P C) (f : A ⇒ T₀ X B) → E._⊙_ h f ≈ h ∙ f
⊙-∙ _ _ = sym-assoc

≤UCᶜ-resp : {f f′ : A ⇒ T₀ X B} {g g′ : A ⇒ T₀ Y B}
          → f ≈ f′ → g ≈ g′ → f ≤UCᶜ g → f′ ≤UCᶜ g′
≤UCᶜ-resp ef eg (s , e) =
  s , E.≈ℰ-trans (E.≈⇒≈ℰ (⟺ ef)) (E.≈ℰ-trans e (E.≈⇒≈ℰ (refl⟩∘⟨ eg)))

UC-composeᶜ : E.UC-compose
UC-composeᶜ {f = f} {g} {h} {k} pf ph =
  ≤UCᶜ-resp (⟺ (⊙-∙ h f)) (⟺ (⊙-∙ k g))
            (≤UC⇒≤UCᶜ (UC-compose (≤UCᶜ⇒≤UC pf) (≤UCᶜ⇒≤UC ph)))
