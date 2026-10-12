{-# OPTIONS --safe --without-K --guardedness #-}

-- The quantitative UC setup of random systems: `UC.Quantitative.Observed` at
-- 𝔾ᴿ, read through the CLOSED verdict slack (`Advantage.Verdict.closure`).
-- 𝔾ᵒ's readout space `spaceᴹ` is the open `_≈ₚ[_]_` and cannot descend to 𝔾ᴿ,
-- whose hom equality is only the limit at zero; the closed one does, and then
-- `≈ᵁ[ ε ]` IS Δ ≤ ε with no slack spent (`≈ᵁᴿ[]⇔∼ᴿ[]`), and the witness at ε
-- IS maurer2011cc Def 3 condition 2 at ε (`≤UCᴿ[]⇔Constructs`), SECURITY-ONLY.
-- Along `rewrite⇒RS`, 𝔾ᴿ's error is the slack closure of 𝔾ᵒ's, one simulator for every slack
-- (`≤UCᴿ[]⇔Witness⁺`).  Morphisms are passed explicitly, for `Construction`'s
-- reason.  See docs/uc-setup-random-systems.md §4.4.
--
-- Exhausts `-M4G`: warm at `-M5G -H1G` it takes 23 s at 2.3 GB residency, of
-- which ~1 GB is the `Observed` application (`UC.Model.Quantitative`'s, at 𝔾ᵒ,
-- exhausts `-M4G` alike).

open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base using (Bool)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Function.Bundles
open import Function.Properties.Equivalence using () renaming (sym to ⇔-sym; trans to ⇔-trans)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Space ℚ-ordered
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Quantitative using (module QUCᵒ)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction
open import CategoricalCrypto.UC.RandomSystems.Morphism
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.Quantitative.Observed as Observed
import CategoricalCrypto.UC.RandomSystems.Setup as Sᴿ

module CategoricalCrypto.UC.RandomSystems.Quantitative where

private
  module G = MonoidalCategory 𝔾ᵒ
  module T = Transfer rewrite⇒RS
  variable
    A B C : Sᵒ.Channel
    X Y P R : Sᵒ.ℐ.Obj
    ε ε′ : ℚ

------------------------------------------------------------------------
-- The closed readout and its setup

spaceᴿ : ApproxSpace 0ℓ 0ℓ
spaceᴿ = record { Carrier = Dₚ Bool ; approx = Verdict.closure }

qevaluationᴿ : QEvaluation (MonoidalCategory.U Sᴿ.𝔾ᴿ) 0ℓ 0ℓ
qevaluationᴿ = record
  { J = 𝟘ᵒ ; Ω = Ωᵒ ; X = spaceᴿ
  ; eval₀ = record { to = Obs ; cong = λ e → Equivalence.from Verdict.≈̄[0]⇔∼ᵃ (∼ᴿ⇒Obs e) }
  }

private module P = AllPositive ℚ-refinement (QEvaluation.approx qevaluationᴿ)

-- Spelled as `UC.Model.Quantitative` spells 𝔾ᵒ's.
module Observedᴿ = Observed Sᴿ.𝔾ᴿ ℚ-ordered qevaluationᴿ P.∼ᵃ-isEquivalence P.zero⇒positive

open Observedᴿ public using () renaming (Q to Qᴿ; QSetup to QSetupᴿ; module Quant to QUCᴿ)

------------------------------------------------------------------------
-- Δ is the quantitative U-agreement, exactly

≈ᵁᴿ[]⇒∼ᴿ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f QUCᴿ.≈ᵁ[ ε ] g → f ∼ᴿ[ ε ] g
≈ᵁᴿ[]⇒∼ᴿ[] {A = A} {X = X} {B = B} {ε = ε} {f = f} {g = g} u d = Verdict.slack λ δ pos →
  ≈ₚ[]-resp (play-cup A (X G.⊗₀ B) f d) (play-cup A (X G.⊗₀ B) g d)
            (Verdict.≈̄⇒≈ (Observedᴿ.≈ᵁ[]⇒≈ℰ[] {ε = ε} u (dualᵒ A) (playᵒ A (X G.⊗₀ B) d) (cupᵒ A)) δ pos)

∼ᴿ[]⇒≈ᵁᴿ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f ∼ᴿ[ ε ] g → f QUCᴿ.≈ᵁ[ ε ] g
∼ᴿ[]⇒≈ᵁᴿ[] {ε = ε} e = Observedᴿ.≈ℰ[]⇒≈ᵁ[] {ε = ε} λ _ t m → close-∼ᴿ[] t m e

≈ᵁᴿ[]⇔∼ᴿ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → (f QUCᴿ.≈ᵁ[ ε ] g) ⇔ (f ∼ᴿ[ ε ] g)
≈ᵁᴿ[]⇔∼ᴿ[] {ε = ε} {f = f} {g = g} =
  mk⇔ (≈ᵁᴿ[]⇒∼ᴿ[] {ε = ε} {f = f} {g = g}) (∼ᴿ[]⇒≈ᵁᴿ[] {ε = ε} {f = f} {g = g})

------------------------------------------------------------------------
-- Security-only construction at ε

infix 4 _≤UCᴿ[_]_

-- maurer2011cc Def 3, condition 2, as the quantitative emulation witness.
_≤UCᴿ[_]_ : A Sᵒ.⇒ Sᵒ.T₀ X B → ℚ → A Sᵒ.⇒ Sᵒ.T₀ Y B → Set₁
f ≤UCᴿ[ ε ] g = QUCᴿ.Witness ε f g

≤UCᴿ[]⇒Constructs : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → f ≤UCᴿ[ ε ] g → Constructs ε f g
≤UCᴿ[]⇒Constructs {ε = ε} {f = f} {g = g} (s , u) = s , ≈ᵁᴿ[]⇒∼ᴿ[] {ε = ε} {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} u

Constructs⇒≤UCᴿ[] : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → Constructs ε f g → f ≤UCᴿ[ ε ] g
Constructs⇒≤UCᴿ[] {ε = ε} {f = f} {g = g} (s , e) = s , ∼ᴿ[]⇒≈ᵁᴿ[] {ε = ε} {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} e

≤UCᴿ[]⇔Constructs : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → (f ≤UCᴿ[ ε ] g) ⇔ Constructs ε f g
≤UCᴿ[]⇔Constructs {ε = ε} {f = f} {g = g} =
  mk⇔ (≤UCᴿ[]⇒Constructs {ε = ε} {f = f} {g = g}) (Constructs⇒≤UCᴿ[] {ε = ε} {f = f} {g = g})

------------------------------------------------------------------------
-- Along `rewrite⇒RS`

-- The image of a hom under `rewrite⇒RS` is the hom itself up to an identity.
≈ᵁᴿ[]-G⇔ : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → (T.G f QUCᴿ.≈ᵁ[ ε ] T.G g) ⇔ (f QUCᴿ.≈ᵁ[ ε ] g)
≈ᵁᴿ[]-G⇔ {f = f} {g = g} = mk⇔
  (QUCᴿ.ctx-resp (QUCᴿ.𝒞.identityˡ {f = f}) (QUCᴿ.𝒞.identityˡ {f = g}))
  (QUCᴿ.ctx-resp (QUCᴿ.𝒞.Equiv.sym (QUCᴿ.𝒞.identityˡ {f = f})) (QUCᴿ.𝒞.Equiv.sym (QUCᴿ.𝒞.identityˡ {f = g})))

≤UCᴿ[]-G⇔ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → (T.G f ≤UCᴿ[ ε ] T.G g) ⇔ (f ≤UCᴿ[ ε ] g)
≤UCᴿ[]-G⇔ {f = f} {g = g} = mk⇔
  (λ (s , u) → s , QUCᴿ.ctx-resp (QUCᴿ.𝒞.identityˡ {f = f}) (QUCᴿ.𝒞.∘-resp-≈ʳ (QUCᴿ.𝒞.identityˡ {f = g})) u)
  (λ (s , u) → s , QUCᴿ.ctx-resp (QUCᴿ.𝒞.Equiv.sym (QUCᴿ.𝒞.identityˡ {f = f}))
                                 (QUCᴿ.𝒞.∘-resp-≈ʳ (QUCᴿ.𝒞.Equiv.sym (QUCᴿ.𝒞.identityˡ {f = g}))) u)

-- 𝔾ᵒ's error crosses unchanged…
≈ᵁ[]⇒≈ᵁᴿ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f QUCᵒ.≈ᵁ[ ε ] g → T.G f QUCᴿ.≈ᵁ[ ε ] T.G g
≈ᵁ[]⇒≈ᵁᴿ[] {ε = ε} {f = f} {g = g} u =
  Equivalence.from (≈ᵁᴿ[]-G⇔ {ε = ε} {f = f} {g = g})
    (∼ᴿ[]⇒≈ᵁᴿ[] {ε = ε} {f = f} {g = g} (≈ᵁ[]⇒∼ᴿ[] {ε = ε} {f = f} {g = g} u))

Witness⇒≤UCᴿ[] : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
               → QUCᵒ.Witness ε f g → T.G f ≤UCᴿ[ ε ] T.G g
Witness⇒≤UCᴿ[] {ε = ε} {f = f} {g = g} w =
  Equivalence.from (≤UCᴿ[]-G⇔ {ε = ε} {f = f} {g = g})
    (Constructs⇒≤UCᴿ[] {ε = ε} {f = f} {g = g} (Witness⇒Constructs {ε = ε} {f = f} {g = g} w))

-- …and 𝔾ᴿ's is the slack closure of 𝔾ᵒ's, with one simulator for every slack.
≈ᵁᴿ[]⇔≈ᵁ[]⁺ : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B}
            → (T.G f QUCᴿ.≈ᵁ[ ε ] T.G g) ⇔ ((δ : ℚ) → 0ℚ ℚ.< δ → f QUCᵒ.≈ᵁ[ ε ℚ.+ δ ] g)
≈ᵁᴿ[]⇔≈ᵁ[]⁺ {ε = ε} {f = f} {g = g} =
  ⇔-trans (≈ᵁᴿ[]-G⇔ {ε = ε} {f = f} {g = g})
          (⇔-trans (≈ᵁᴿ[]⇔∼ᴿ[] {ε = ε} {f = f} {g = g}) (∼ᴿ[]⇔≈ᵁ[] {ε = ε} {f = f} {g = g}))

≤UCᴿ[]⇔Witness⁺ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
                → (T.G f ≤UCᴿ[ ε ] T.G g) ⇔ Witness⁺ ε f g
≤UCᴿ[]⇔Witness⁺ {ε = ε} {f = f} {g = g} =
  ⇔-trans (≤UCᴿ[]-G⇔ {ε = ε} {f = f} {g = g})
          (⇔-trans (≤UCᴿ[]⇔Constructs {ε = ε} {f = f} {g = g}) (Constructs⇔Witness⁺ {ε = ε} {f = f} {g = g}))

-- At zero it is 𝔾ᴿ's qualitative emulation.
≤UCᴿ⇔≤UCᴿ[0] : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
              → (T.G f Sᴿ.≤UC T.G g) ⇔ (f ≤UCᴿ[ 0ℚ ] g)
≤UCᴿ⇔≤UCᴿ[0] {f = f} {g = g} =
  ⇔-trans (≤UCᴿ⇔Constructs₀ {f = f} {g = g}) (⇔-sym (≤UCᴿ[]⇔Constructs {ε = 0ℚ} {f = f} {g = g}))

------------------------------------------------------------------------
-- maurer2011cc Thm 1 at a slack

≤UCᴿ[]-refl : (f : A Sᵒ.⇒ Sᵒ.T₀ X B) → f ≤UCᴿ[ 0ℚ ] f
≤UCᴿ[]-refl f = Constructs⇒≤UCᴿ[] {ε = 0ℚ} {f = f} {g = f} (constructs-refl f)

≤UCᴿ[]-trans : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} {h : A Sᵒ.⇒ Sᵒ.T₀ P B}
             → f ≤UCᴿ[ ε ] g → g ≤UCᴿ[ ε′ ] h → f ≤UCᴿ[ ε ℚ.+ ε′ ] h
≤UCᴿ[]-trans {ε = ε} {ε′ = ε′} {f = f} {g = g} {h = h} w w′ =
  Constructs⇒≤UCᴿ[] {ε = ε ℚ.+ ε′} {f = f} {g = h}
    (constructs-trans {ε = ε} {ε′ = ε′} {f = f} {g = g} {h = h}
      (≤UCᴿ[]⇒Constructs {ε = ε} {f = f} {g = g} w) (≤UCᴿ[]⇒Constructs {ε = ε′} {f = g} {g = h} w′))

≤UCᴿ[]-∙ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
           {u : B Sᵒ.⇒ Sᵒ.T₀ P C} {v : B Sᵒ.⇒ Sᵒ.T₀ R C}
         → f ≤UCᴿ[ ε ] g → u ≤UCᴿ[ ε′ ] v → (u Sᵒ.∙ f) ≤UCᴿ[ ε′ ℚ.+ ε ] (v Sᵒ.∙ g)
≤UCᴿ[]-∙ {ε = ε} {ε′ = ε′} {f = f} {g = g} {u = u} {v = v} wf wu =
  Constructs⇒≤UCᴿ[] {ε = ε′ ℚ.+ ε} {f = u Sᵒ.∙ f} {g = v Sᵒ.∙ g}
    (constructs-∙ {ε = ε} {ε′ = ε′} {f = f} {g = g} {u = u} {v = v}
      (≤UCᴿ[]⇒Constructs {ε = ε} {f = f} {g = g} wf) (≤UCᴿ[]⇒Constructs {ε = ε′} {f = u} {g = v} wu))
