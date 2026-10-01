{-# OPTIONS --safe --without-K #-}

-- The observed quantitative setup: tests compared through every closure at a
-- measured error (`docs/quantitative-uc-setup-plan.typ` §6).
--
-- This is `Observable`'s comparison with the slack still VISIBLE, so the
-- qualitative test presheaf is recovered by forgetting the error: at `qual`
-- the two are the same relation, at `qual₊` (`Q₊⇔ℰ₊`) and against
-- `Standard2.StdUC`'s agreement (`≈ℰ[]⇔≈ᵁ[]`) they differ by the order of two
-- quantifiers and nothing else.  The only quantitative input is `read-resp₀`,
-- which reads the ambient hom equality EXACTLY: hence `splice`, and hence a
-- nonexpansive pullback.
--
-- ALL closures are admitted, and no claim is made that these errors agree with
-- the allowance-restricted ones of `UC.Quantitative.Query`.
--
-- The COARSENING is a parameter, not `qual₊`: a tier whose readout keeps an
-- error witness of its own (`UC.Family.Negligible.Evaluationᴺ`) is one too, and
-- there the comparison with `_∼_` costs `induces` and its converse `reflects`,
-- each gating one block below.  At `qual₊` — the route both models take, where
-- `_∼_` IS closeness at every positive error — both hold by definition and
-- `Q₊⇔ℰ₊` is the unconditional statement.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal.CurriedTensor
open import Categories.Functor.Presheaf using (Presheaf)
import Categories.Morphism.Reasoning as MR

open import Function.Bundles using (Func; _⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error
  using (Approximation; OrderedErrorAlgebra; Refinement; ≈[]-resp₀)
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)

import CategoricalCrypto.Approx.Error as Errorᴹ
import CategoricalCrypto.Approx.Evaluation as Evaluationᴹ
import CategoricalCrypto.Approx.Forget as Forgetᴹ
import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Quantitative.Observed
  {o ℓ e cs ℓs es ℓe ℓa : Level} (M : MonoidalCategory o ℓ e)
  (E : OrderedErrorAlgebra es ℓe)
  (qro : Evaluationᴹ.QEvaluation E (MonoidalCategory.U M) cs (es ⊔ ℓe ⊔ ℓa))
  {_∼_ : Rel (Evaluationᴹ.QEvaluation.Carrier qro) ℓs}
  (∼-isEquivalence : IsEquivalence _∼_)
  (∼-from-zero : {x y : Evaluationᴹ.QEvaluation.Carrier qro}
    → Evaluationᴹ.QEvaluation._≈[_]_ qro x (OrderedErrorAlgebra.ε₀ E) y → x ∼ y)
  where

open import CategoricalCrypto.Approx.Evaluation E using (qual₊; qualBy)
open import CategoricalCrypto.Approx.Space E

private module Qr = Evaluationᴹ.QEvaluation qro

readout : Evaluation (MonoidalCategory.U M) cs ℓs
readout = qualBy qro ∼-isEquivalence ∼-from-zero

open import CategoricalCrypto.UC.Quantitative E
open import CategoricalCrypto.UC.Quantitative.Bridge E

open Evaluation readout
open Observable observable using (Test; _≋_; ℰᴼ)
open Std2.StdUC M ℰᴼ
open Approximation Qr.approx
open Qr using (read-resp₀)
open HomReasoning
open MR ∣machines∣

private variable
  A B X : Channel
  ε : Error

private
  -- Every rebracketing below is EXACT, so it enters a bound at either endpoint
  -- and the bound crosses unchanged.
  splice : {u u′ v v′ : Closure Ω}
         → u ≈ u′ → v ≈ v′ → read u′ ≈[ ε ] read v′ → read u ≈[ ε ] read v
  splice p q = ≈[]-resp₀ E Qr.approx (read-resp₀ p) (read-resp₀ (⟺ q))

------------------------------------------------------------------------
-- Tests at a measured error

infix 4 _≈ᵗ[_]_

_≈ᵗ[_]_ : Test A → Error → Test A → Set (es ⊔ ℓe ⊔ ℓ ⊔ ℓa)
_≈ᵗ[_]_ {A} E₁ ε E₂ = (m : Closure A) → observe E₁ m ≈[ ε ] observe E₂ m

approxᵗ : (A : Channel) → Approximation (Test A) E (es ⊔ ℓe ⊔ ℓ ⊔ ℓa)
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
  -- Each presheaf law is the ambient hom equality read at zero error.
  cast : {E₁ E₂ : Test A} → E₁ ≈ E₂ → E₁ ≈ᵗ[ ε₀ ] E₂
  cast eq _ = read-resp₀ (∘-resp-≈ˡ eq)

Q : Presheaf ∣machines∣ (Approx ℓ (es ⊔ ℓe ⊔ ℓ ⊔ ℓa))
Q = record
  { F₀ = spaceᵗ
  ; F₁ = λ h → record
      { map = _∘ h ; preserves = λ hyp m → splice assoc assoc (hyp (h ∘ m)) }
  ; identity     = λ _ → cast identityʳ
  ; homomorphism = λ _ → cast sym-assoc
  ; F-resp-≈     = λ eq _ → cast (∘-resp-≈ʳ eq)
  }

-- `𝒞` is spelled as in `curriedTensor M`'s type.  `ℳ-standard` is the same
-- functor, but its type names the category through `StdUC`'s own copy of `U`,
-- and any spelling mismatch there sends conversion through the unfolded
-- `Endofunctors` record (5.8 s against 0.1 s).
QSetup : QUCSetup o ℓ e o ℓ e ℓ (ℓ ⊔ ℓa)
QSetup = record { 𝒞 = MonoidalCategory.U M ; ℐ = M ; ℳ = curriedTensor M ; Q = Q }

-- The quantitative metatheory at this instance.  Named rather than opened: a
-- consumer that also opens the qualitative theory would see each name twice.
module Quant = QBridge QSetup

------------------------------------------------------------------------
-- …and the core's ancilla-quantified agreement, with the error kept

infix 4 _≈ℰ[_]_

_≈ℰ[_]_ : (f : A ⇒ B) → Error → (g : A ⇒ B) → Set (o ⊔ ℓ ⊔ es ⊔ ℓe ⊔ ℓa)
_≈ℰ[_]_ {A} {B} f ε g = (Y : Channel) (Et : Test (Y ⊗₀ B)) (m : Closure (Y ⊗₀ A))
                      → observe (Et ∘ id ⊗₁ f) m ≈[ ε ] observe (Et ∘ id ⊗₁ g) m

-- The ancilla of the one relation is the grade of the other, and the two tests
-- differ by the associator alone.
≈ℰ[]⇒≈ᵁ[] : {f g : A ⇒ T₀ X B} → f ≈ℰ[ ε ] g → f Quant.≈ᵁ[ ε ] g
≈ℰ[]⇒≈ᵁ[] h W t m = splice (sym-assoc ⟩∘⟨refl) (sym-assoc ⟩∘⟨refl) (h W (t ∘ α⇐) m)

≈ᵁ[]⇒≈ℰ[] : {f g : A ⇒ T₀ X B} → f Quant.≈ᵁ[ ε ] g → f ≈ℰ[ ε ] g
≈ᵁ[]⇒≈ℰ[] u Y Et m = splice (⟺ (pullʳ (cancelˡ associator.isoʳ) ⟩∘⟨refl))
                              (⟺ (pullʳ (cancelˡ associator.isoʳ) ⟩∘⟨refl)) (u Y (Et ∘ α⇒) m)

≈ℰ[]⇔≈ᵁ[] : {f g : A ⇒ T₀ X B} → (f ≈ℰ[ ε ] g) ⇔ (f Quant.≈ᵁ[ ε ] g)
≈ℰ[]⇔≈ᵁ[] = mk⇔ ≈ℰ[]⇒≈ᵁ[] ≈ᵁ[]⇒≈ℰ[]

------------------------------------------------------------------------
-- …and forgetting the error gives the qualitative test presheaf back

-- The EXACT forgetting IS the test presheaf of `qual`; the all-positive one
-- is that of `qual₊` up to the order of the closure quantifier and the error
-- one.  Neither costs `induces`; the coarsening `_∼_` this module is
-- parameterized by is what does.
module AllPositive (R : Refinement E) where

  open Refinement R using (Positive)
  open Forgetᴹ E R ℓ (ℓ ⊔ ℓa) using (⟦_⟧₊)
  open Errorᴹ.AllPositive R Qr.approx using (_∼ᵃ_)

  private module Plus = Evaluation (qual₊ R qro)

  Q₊⇔ℰ₊ : {E₁ E₂ : Test A}
        → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
        ⇔ Setoid._≈_ (Functor.₀ Plus.Pᴱ A) (Plus.transpose E₁) (Plus.transpose E₂)
  Q₊⇔ℰ₊ = mk⇔ (λ h m ε pos → h ε pos m) (λ h ε pos m → h m ε pos)

  -- …and what the comparison with `_∼_` costs.
  module Absorbing (induces : {x y : Qr.Carrier} → x ∼ᵃ y → x ∼ y) where

    ∼₊⇒≋ : {E₁ E₂ : Test A} → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂ → E₁ ≋ E₂
    ∼₊⇒≋ h m = induces λ ε pos → h ε pos m

    -- `_≈ℰ[ ε ]_` is where a security statement is PROVED, `_≈ᵁ_` where one
    -- lands, and this is `induces` read at the environment level.  The slack
    -- may not depend on a budget here; that is one layer up, at
    -- `UC.Family.absorb`.
    absorbᵘ : {f g : A ⇒ T₀ X B} → ((ε : Error) → Positive ε → f ≈ℰ[ ε ] g) → f ≈ᵁ g
    absorbᵘ h Y = KE.mk∼ λ {Et} m → induces λ ε pos → ≈ℰ[]⇒≈ᵁ[] (h ε pos) Y Et m

    -- …and with the converse the qualitative test presheaf is the `F₊` image.
    module Reflecting (reflects : {x y : Qr.Carrier} → x ∼ y → x ∼ᵃ y) where

      ≋⇒∼₊ : {E₁ E₂ : Test A} → E₁ ≋ E₂ → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
      ≋⇒∼₊ h ε pos m = reflects (h m) ε pos

      ≋⇔∼₊ : {E₁ E₂ : Test A} → (E₁ ≋ E₂) ⇔ Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E₁ E₂
      ≋⇔∼₊ = mk⇔ ≋⇒∼₊ ∼₊⇒≋
