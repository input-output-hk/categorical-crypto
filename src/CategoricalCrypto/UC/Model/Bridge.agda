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
-- in its statement, and instantiating that quantifier at `id` takes it back.
--
-- Universal composition is what the identification RETIRES.  `UC.Emulation`
-- could only state it, the chain needing a `sub`/`T₁` interchange and an
-- `a⇒`-naturality that `Grading` does not ask for; here the graded composite IS
-- the Kleisli one (`ext X h` is `α⇐ ∘ id ⊗₁ h` on the nose,
-- `CurriedTensor.Properties.ext-⊗`), so `≤UCᶜ⇔≤UC` carries `UC-compose` —
-- already a theorem — across, and there is nothing left for the core to owe.
--
-- At UNGRADED homs `_≈ᵁ_` says nothing — it is stated at `A ⇒ T₀ X B` — and the
-- core's relation is stated at every codomain.  What it is there is `_≈ᴳ_`, the
-- bare kernel stabilized under the action: exactly the property `GradeStable`
-- asks of `_≈ℰ_` and this model does not supply.  `_≈ᴳ_` agrees with `_≈ᵁ_`
-- wherever the latter is stated, so the seam can be read in one vocabulary.
--
-- Nothing here unfolds the seal: the core's `UCBase` is assembled from
-- `UC.Core.Standard.gradingᵗ` at `𝔾ᵒ` and `UC.Model.Observation`, both of which
-- name the sealed bundle without opening it.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗; μ-α⇐)
import Categories.Morphism.Reasoning as MR

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
open MR ∣machines∣ using (cancelˡ)

private variable A B C X Y : Channel

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

≤UCᶜ⇒≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g → f ≤UC g
≤UCᶜ⇒≤UC p a = let s , e = E.dummy-complete p a in s , ≈ℰᶜ⇒≈ᵁ e

≤UC⇒≤UCᶜ : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UC g → f ≤UCᶜ g
≤UC⇒≤UCᶜ {f = f} p =
  let s , e = p id in s , ≈ᵁ⇒≈ℰᶜ (≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ f))) e)

≤UCᶜ⇔≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g ⇔ f ≤UC g
≤UCᶜ⇔≤UC {f = f} {g} = mk⇔ {B = f ≤UC g} ≤UCᶜ⇒≤UC ≤UC⇒≤UCᶜ

------------------------------------------------------------------------
-- The three instruments the seam consumes, over the inherited kernel

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

-- `UC.Emulation.blind-grade`: an emulation at a grade every simulator is blind
-- to IS a plain agreement.  `_≤UC_` carries the dummy quantifier in its
-- statement here, so the core's degrading step is its instantiation at `id`.
blind-gradeᵁ : {f g : A ⇒ T₀ X B} → ((s : X ⇒ X) → sub s ∘ g ≈ᵁ g) → f ≤UC g → f ≈ᵁ g
blind-gradeᵁ {f = f} blind p =
  let s , e = p id
  in ≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ f))) (≈ᵁ-trans e (blind s))

-- `UC.Emulation.unit-grade`: …and if the wire inflating a closed process to
-- that grade is absorbed by the ancilla quantifier too, the emulation is an
-- agreement of the UNGRADED processes.  Both hypotheses are degeneracy facts
-- about the chosen grade, not about the emulation.
unit-gradeᵁ : {ι : B ⇒ T₀ X B} {u v : A ⇒ B}
            → ((s : X ⇒ X) → sub s ∘ (ι ∘ v) ≈ᵁ ι ∘ v)
            → (ι ∘ u ≈ᵁ ι ∘ v → u ≈ᴳ v)
            → ι ∘ u ≤UC ι ∘ v → u ≈ᴳ v
unit-gradeᵁ blind reflect e = reflect (blind-gradeᵁ blind e)
