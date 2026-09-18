{-# OPTIONS --safe --without-K #-}

-- The observed quantitative setup: tests compared through every closure at a
-- measured error (`docs/quantitative-uc-setup-plan.typ` §6).
--
-- This is `UC.Environment.Presheaf`'s comparison with the slack still VISIBLE,
-- so that presheaf is recovered as the `F₊` image (`≋⇔∼₊`) and
-- `UC.Core.Bridge`'s agreement as `≈ℰ[]⇔≈ᵁ[]` — in both cases the two sides
-- differ by the order of two quantifiers and nothing else.  The only
-- quantitative input is `⟦⟧-resp-≈₀`, which observes the ambient hom equality
-- EXACTLY: hence `splice`, and hence a nonexpansive pullback.
--
-- ALL closures are admitted, and no claim is made that these errors agree with
-- the allowance-restricted ones of `UC.Quantitative.Query`.
--
-- `reflects` is the converse of `induces`, and holds by definition at the
-- observation `UC.Approximate.Induced` constructs — the route both models take
-- — where `_∼_` IS closeness at every positive error.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)

open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra; ≈[]-resp₀)
open import CategoricalCrypto.UC.Approximate
  using (ApproximateObservation; Approximation)
open import CategoricalCrypto.UC.Core using (Observation)

module CategoricalCrypto.UC.Quantitative.Observed
  {o ℓ e os ℓs es ℓe ℓa : Level} (M : MonoidalCategory o ℓ e)
  (E : OrderedErrorAlgebra es ℓe) (O : Observation (MonoidalCategory.U M) os ℓs)
  (apx : ApproximateObservation O (OrderedErrorAlgebra.errors E) (es ⊔ ℓe ⊔ ℓa))
  (reflects : {x y : Observation.Obs O}
            → Observation._∼_ O x y → ApproximateObservation._∼ᵃ_ apx x y)
  where

open import CategoricalCrypto.Approx.Forget E ℓ (ℓ ⊔ ℓa)
open import CategoricalCrypto.Approx.Space E
open import CategoricalCrypto.UC.Core.Bridge M O
open import CategoricalCrypto.UC.Quantitative E
open import CategoricalCrypto.UC.Quantitative.Bridge E

open ApproximateObservation apx
open Observation O
open OrderedErrorAlgebra E using (errors)
open C using (Test; Closure; obs; tv₁; _≋_)
open HomReasoning

private variable
  A B X : Channel
  ε : Error

private
  -- Every rebracketing below is EXACT, so it enters a bound at either endpoint
  -- and the bound crosses unchanged.
  splice : {u u′ v v′ : Closure Ω}
         → u ≈ u′ → v ≈ v′ → ⟦ u′ ⟧ ≈[ ε ] ⟦ v′ ⟧ → ⟦ u ⟧ ≈[ ε ] ⟦ v ⟧
  splice p q = ≈[]-resp₀ E approx (⟦⟧-resp-≈₀ p) (⟦⟧-resp-≈₀ (⟺ q))

------------------------------------------------------------------------
-- Tests at a measured error

infix 4 _≈ᵗ[_]_

_≈ᵗ[_]_ : Test A → Error → Test A → Set (es ⊔ ℓe ⊔ ℓ ⊔ ℓa)
_≈ᵗ[_]_ {A} E₁ ε E₂ = (m : Closure A) → obs E₁ m ≈[ ε ] obs E₂ m

approxᵗ : (A : Channel) → Approximation (Test A) errors (es ⊔ ℓe ⊔ ℓ ⊔ ℓa)
approxᵗ A = record
  { _≈[_]_    = _≈ᵗ[_]_
  ; ≈[]-refl  = λ _ → ≈[]-refl
  ; ≈[]-sym   = λ h m → ≈[]-sym (h m)
  ; ≈[]-trans = λ h k m → ≈[]-trans (h m) (k m)
  ; ≈[]-mono  = λ le h m → ≈[]-mono le (h m)
  }

spaceᵗ : Channel → ApproxSpace ℓ (es ⊔ ℓe ⊔ ℓ ⊔ ℓa)
spaceᵗ A = record { Carrier = Test A ; approx = approxᵗ A }

private
  -- Each presheaf law is the ambient hom equality observed at zero error.
  cast : {E₁ E₂ : Test A} → E₁ ≈ E₂ → E₁ ≈ᵗ[ ε₀ ] E₂
  cast eq _ = ⟦⟧-resp-≈₀ (∘-resp-≈ˡ eq)

Q : Presheaf ∣machines∣ (Approx ℓ (es ⊔ ℓe ⊔ ℓ ⊔ ℓa))
Q = record
  { F₀ = spaceᵗ
  ; F₁ = λ h → record
      { map = _∘ h ; preserves = λ hyp m → splice assoc assoc (hyp (h ∘ m)) }
  ; identity     = λ _ → cast identityʳ
  ; homomorphism = λ _ → cast sym-assoc
  ; F-resp-≈     = λ eq _ → cast (∘-resp-≈ʳ eq)
  }

QSetup : QUCSetup o ℓ e o ℓ e ℓ (ℓ ⊔ ℓa)
QSetup = record { 𝒞 = ∣machines∣ ; ℐ = M ; ℳ = ℳ-standard ; Q = Q }

-- The quantitative metatheory at this instance.  Named rather than opened: a
-- consumer that also opens the qualitative theory would see each name twice.
module Quant = QBridge QSetup

------------------------------------------------------------------------
-- …and the `F₊` image is the qualitative test presheaf

≋⇒∼₊ : {E₁ E₂ : Test A} → E₁ ≋ E₂ → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
≋⇒∼₊ h ε pos m = reflects (h m) ε pos

∼₊⇒≋ : {E₁ E₂ : Test A} → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂ → E₁ ≋ E₂
∼₊⇒≋ h m = induces λ ε pos → h ε pos m

≋⇔∼₊ : {E₁ E₂ : Test A} → (E₁ ≋ E₂) ⇔ Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
≋⇔∼₊ = mk⇔ ≋⇒∼₊ ∼₊⇒≋

------------------------------------------------------------------------
-- …and the core's ancilla-quantified agreement, with the error kept

infix 4 _≈ℰ[_]_

_≈ℰ[_]_ : (f : A ⇒ B) → Error → (g : A ⇒ B) → Set (o ⊔ ℓ ⊔ es ⊔ ℓe ⊔ ℓa)
_≈ℰ[_]_ {A} {B} f ε g = (Y : Channel) (Et : Test (Y ⊗₀ B)) (m : Closure (Y ⊗₀ A))
                      → obs (tv₁ Y f Et) m ≈[ ε ] obs (tv₁ Y g Et) m

-- `UC.Core.Bridge.≈ℰᶜ⇔≈ᵁ` at every error: the ancilla of the one relation is
-- the grade of the other, and the two tests differ by the associator alone.
≈ℰ[]⇒≈ᵁ[] : {f g : A ⇒ T₀ X B} → f ≈ℰ[ ε ] g → f Quant.≈ᵁ[ ε ] g
≈ℰ[]⇒≈ᵁ[] {f = f} {g = g} h W t m =
  splice (shuffle⇐ f t m ○ sym-assoc) (shuffle⇐ g t m ○ sym-assoc)
         (h W (t ∘ α⇐) m)

≈ᵁ[]⇒≈ℰ[] : {f g : A ⇒ T₀ X B} → f Quant.≈ᵁ[ ε ] g → f ≈ℰ[ ε ] g
≈ᵁ[]⇒≈ℰ[] {f = f} {g = g} u Y Et m =
  splice (⟺ (shuffle⇒ f Et m ○ sym-assoc)) (⟺ (shuffle⇒ g Et m ○ sym-assoc))
         (u Y (Et ∘ α⇒) m)

≈ℰ[]⇔≈ᵁ[] : {f g : A ⇒ T₀ X B} → (f ≈ℰ[ ε ] g) ⇔ (f Quant.≈ᵁ[ ε ] g)
≈ℰ[]⇔≈ᵁ[] = mk⇔ ≈ℰ[]⇒≈ᵁ[] ≈ᵁ[]⇒≈ℰ[]

-- `induces` read at the environment level: closeness at every positive error
-- IS the core's agreement — `positive-agreement⇐` across the equivalence above.
absorbᵘ : {f g : A ⇒ B} → ((ε : Error) → Positive ε → f ≈ℰ[ ε ] g) → f ≈ℰᶜ g
absorbᵘ h Y Et m = induces λ ε pos → h ε pos Y Et m
