{-# OPTIONS --safe --without-K --guardedness #-}

-- The construction notion of constructive cryptography (maurer2011cc §5.1
-- Def 3, the security condition) over 𝔾ᵒ: "f constructs within ε what g
-- does behind a simulator s" is `Constructs ε f g`.  At ε = 0 it IS
-- UC-emulation, in protocol-rewrite and, along `rewrite⇒RS`, in random
-- systems (`≤UC⇔Constructs₀`, `≤UCᴿ⇔Constructs₀`); at ε it is the slack
-- closure of `UC.Quantitative.Observed`'s witness at 𝔾ᵒ, with one simulator
-- for every slack (`Constructs⇔Witness⁺`).  It composes as maurer2011cc
-- Thm 1 says.  See docs/uc-setup-random-systems.md §4.4.
--
-- The morphisms of `_≤UC_`, `_≈ᵁ_` and `At` are passed explicitly: inferred,
-- they are solved by unfolding those relations at the concrete 𝔾ᵒ, and
-- `≤UC⇔Constructs₀` alone exhausted a 4 GiB heap.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext using (0<½*)
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Approx.Rational
open import CategoricalCrypto.UC.Model.Quantitative
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction
open import CategoricalCrypto.UC.RandomSystems.Morphism
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.RandomSystems.Setup as Sᴿ

module CategoricalCrypto.UC.RandomSystems.Construction where

private
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ
  variable
    A B C : Sᵒ.Channel
    X Y Z P R : Sᵒ.ℐ.Obj
    ε ε′ : ℚ

------------------------------------------------------------------------
-- Δ against the quantitative U-agreement of `UC.Model.Quantitative`

-- The cup closure plays the strategy (`FullAbstraction.play-cup`).
≈ᵁ[]⇒∼ᴿ[] : {A B : Sᵒ.Channel} {X : Sᵒ.ℐ.Obj} {ε : ℚ} {f g : A Sᵒ.⇒ Sᵒ.T₀ X B}
          → f QUCᵒ.≈ᵁ[ ε ] g → f ∼ᴿ[ ε ] g
≈ᵁ[]⇒∼ᴿ[] {A} {B} {X} {ε} {f} {g} u d =
  Verdict.≈⇒≈̄ (≈ₚ[]-resp (play-cup A (X G.⊗₀ B) f d) (play-cup A (X G.⊗₀ B) g d)
                          (≈ᵁ[]⇒≈ℰ[] {ε = ε} u (dualᵒ A) (playᵒ A (X G.⊗₀ B) d) (cupᵒ A)))

-- A closing context observes no more than Δ (`Composition.close-∼ᴿ[]`), up to
-- the slack the closure leaves.
∼ᴿ[]⇒≈ᵁ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f ∼ᴿ[ ε ] g → (δ : ℚ) → 0ℚ ℚ.< δ → f QUCᵒ.≈ᵁ[ ε ℚ.+ δ ] g
∼ᴿ[]⇒≈ᵁ[] {ε = ε} e δ pos = ≈ℰ[]⇒≈ᵁ[] {ε = ε ℚ.+ δ} λ _ t m → Verdict.≈̄⇒≈ (close-∼ᴿ[] t m e) δ pos

∼ᴿ[]⇔≈ᵁ[] : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B}
          → (f ∼ᴿ[ ε ] g) ⇔ ((δ : ℚ) → 0ℚ ℚ.< δ → f QUCᵒ.≈ᵁ[ ε ℚ.+ δ ] g)
∼ᴿ[]⇔≈ᵁ[] {ε = ε} = mk⇔ ∼ᴿ[]⇒≈ᵁ[]
  λ h d → Verdict.≈̄-closed λ δ pos → ≈ᵁ[]⇒∼ᴿ[] {ε = ε ℚ.+ δ} (h δ pos) d

------------------------------------------------------------------------
-- The construction notion

-- maurer2011cc Def 3, condition 2, with d = Δ over every `Strat`: the real
-- f is within ε of the ideal g behind the simulator s.
Constructs : ℚ → A Sᵒ.⇒ Sᵒ.T₀ X B → A Sᵒ.⇒ Sᵒ.T₀ Y B → Set₁
Constructs {X = X} {Y = Y} ε f g = Σ[ s ∈ Y Sᵒ.ℐ.⇒ X ] f ∼ᴿ[ ε ] (Sᵒ.sub s Sᵒ.∘ g)

≤UC⇒Constructs₀ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → f Sᵒ.≤UC g → Constructs 0ℚ f g
≤UC⇒Constructs₀ {f = f} {g = g} le =
  let s , u = Sᵒ.≤UC⇒dummy {f = f} {g = g} le
  in s , Equivalence.to (∼ᴿ⇔∼ᴿ[0] {f = f} {g = Sᵒ.sub s Sᵒ.∘ g}) (≈ᵁ⇒≈ᴿ {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} u)

Constructs₀⇒≤UC : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → Constructs 0ℚ f g → f Sᵒ.≤UC g
Constructs₀⇒≤UC {f = f} {g = g} (s , e) =
  Sᵒ.dummy-complete {f = f} {g = g}
    (s , ≈ᴿ⇒≈ᵁ {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} (Equivalence.from (∼ᴿ⇔∼ᴿ[0] {f = f} {g = Sᵒ.sub s Sᵒ.∘ g}) e))

≤UC⇔Constructs₀ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → (f Sᵒ.≤UC g) ⇔ Constructs 0ℚ f g
≤UC⇔Constructs₀ {f = f} {g = g} = mk⇔ (≤UC⇒Constructs₀ {f = f} {g = g}) (Constructs₀⇒≤UC {f = f} {g = g})

-- 𝔾ᴿ's `≈ᵁ` is `∼ᴿ` because `ν` is mono, and `rewrite⇒RS`'s `κ` is an identity.
≈ᵁᴿ⇒∼ᴿ : {f g : A Sᴿ.⇒ Sᴿ.T₀ X B} → f Sᴿ.≈ᵁ g → f Q.∼ g
≈ᵁᴿ⇒∼ᴿ {f = f} {g = g} u = ≈ᵁ⇒≈ᴿ {f = f} {g = g} λ W → Transfer.mono⇒reflects-≈ℰ rewrite⇒RS mono (u W)
  where mono = descendᵛ-mono 𝔾ᵒ congᴿ Sᵒ.ℰᵒ Sᴿ.∼ᴿ⇒≋

≤UCᴿ⇒Constructs₀ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
                 → Transfer.G rewrite⇒RS f Sᴿ.≤UC Transfer.G rewrite⇒RS g → Constructs 0ℚ f g
≤UCᴿ⇒Constructs₀ {f = f} {g = g} le =
  let s , u = Sᴿ.≤UC⇒dummy {f = f} {g = g}
                (Sᴿ.≤UC-resp-≈ {f = Transfer.G rewrite⇒RS f} {f′ = f} {g = Transfer.G rewrite⇒RS g} {g′ = g}
                               (Sᴿ.𝒞.identityˡ {f = f}) (Sᴿ.𝒞.identityˡ {f = g}) le)
  in s , Equivalence.to (∼ᴿ⇔∼ᴿ[0] {f = f} {g = Sᵒ.sub s Sᵒ.∘ g}) (≈ᵁᴿ⇒∼ᴿ {f = f} {g = Sᴿ.sub s Sᴿ.∘ g} u)

Constructs₀⇒≤UCᴿ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
                 → Constructs 0ℚ f g → Transfer.G rewrite⇒RS f Sᴿ.≤UC Transfer.G rewrite⇒RS g
Constructs₀⇒≤UCᴿ {f = f} {g = g} (s , e) =
  Sᴿ.≤UC-resp-≈ {f = f} {f′ = Transfer.G rewrite⇒RS f} {g = g} {g′ = Transfer.G rewrite⇒RS g}
    (Sᴿ.𝒞.Equiv.sym (Sᴿ.𝒞.identityˡ {f = f})) (Sᴿ.𝒞.Equiv.sym (Sᴿ.𝒞.identityˡ {f = g}))
    (Sᴿ.dummy-complete {f = f} {g = g}
      (s , Sᴿ.≈C⇒≈ᵁ {f = f} {g = Sᴿ.sub s Sᴿ.∘ g}
             (Equivalence.from (∼ᴿ⇔∼ᴿ[0] {f = f} {g = Sᵒ.sub s Sᵒ.∘ g}) e)))

≤UCᴿ⇔Constructs₀ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
                 → (Transfer.G rewrite⇒RS f Sᴿ.≤UC Transfer.G rewrite⇒RS g) ⇔ Constructs 0ℚ f g
≤UCᴿ⇔Constructs₀ {f = f} {g = g} = mk⇔ (≤UCᴿ⇒Constructs₀ {f = f} {g = g}) (Constructs₀⇒≤UCᴿ {f = f} {g = g})

-- At ε it is `UC.Quantitative.Observed`'s witness up to every positive slack,
-- the simulator fixed before the slack.
Witness⁺ : ℚ → A Sᵒ.⇒ Sᵒ.T₀ X B → A Sᵒ.⇒ Sᵒ.T₀ Y B → Set₁
Witness⁺ {X = X} {Y = Y} ε f g = Σ[ s ∈ Y Sᵒ.ℐ.⇒ X ] ((δ : ℚ) → 0ℚ ℚ.< δ → QUCᵒ.At s (ε ℚ.+ δ) f g)

Constructs⇒Witness⁺ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → Constructs ε f g → Witness⁺ ε f g
Constructs⇒Witness⁺ {ε = ε} {f = f} {g = g} (s , e) = s , ∼ᴿ[]⇒≈ᵁ[] {ε = ε} {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} e

Witness⁺⇒Constructs : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → Witness⁺ ε f g → Constructs ε f g
Witness⁺⇒Constructs {ε = ε} {f = f} {g = g} (s , h) =
  s , Equivalence.from (∼ᴿ[]⇔≈ᵁ[] {ε = ε} {f = f} {g = Sᵒ.sub s Sᵒ.∘ g}) h

Constructs⇔Witness⁺ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} → Constructs ε f g ⇔ Witness⁺ ε f g
Constructs⇔Witness⁺ {ε = ε} {f = f} {g = g} =
  mk⇔ (Constructs⇒Witness⁺ {ε = ε} {f = f} {g = g}) (Witness⁺⇒Constructs {ε = ε} {f = f} {g = g})

Witness⇒Constructs : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
                   → QUCᵒ.Witness ε f g → Constructs ε f g
Witness⇒Constructs {ε = ε} {f = f} {g = g} (s , u) = s , ≈ᵁ[]⇒∼ᴿ[] {ε = ε} {f = f} {g = Sᵒ.sub s Sᵒ.∘ g} u

------------------------------------------------------------------------
-- maurer2011cc Thm 1

constructs-refl : (f : A Sᵒ.⇒ Sᵒ.T₀ X B) → Constructs 0ℚ f f
constructs-refl f =
  Sᵒ.ℐ.id , ≈⇒∼ᴿ[0] {f = f} {g = Sᵒ.sub Sᵒ.ℐ.id Sᵒ.∘ f} (G.Equiv.sym (Sᵒ.sub-identityˡ f))

-- The simulators compose in the order fn. 15 there notes.
constructs-trans : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B} {h : A Sᵒ.⇒ Sᵒ.T₀ Z B}
                 → Constructs ε f g → Constructs ε′ g h → Constructs (ε ℚ.+ ε′) f h
constructs-trans {ε = ε} {ε′ = ε′} {f = f} {g = g} {h = h} (s , e) (t , e′) =
  s Sᵒ.ℐ.∘ t ,
  ≈ᴿ[]-mono (≤-reflexive (cong (ε ℚ.+_) (trans (+-identityʳ (0ℚ ℚ.+ ε′)) (+-identityˡ ε′))))
    (≈ᴿ[]-trans e
      (≈ᴿ[]-trans (∘-resp-∼ᴿ[] {f = Sᵒ.sub s} {h = Sᵒ.sub s} {g = g} {i = Sᵒ.sub t Sᵒ.∘ h}
                               (≈⇒∼ᴿ[0] {f = Sᵒ.sub s} {g = Sᵒ.sub s} G.Equiv.refl) e′)
                  (≈⇒∼ᴿ[0] {f = Sᵒ.sub s Sᵒ.∘ (Sᵒ.sub t Sᵒ.∘ h)} {g = Sᵒ.sub (s Sᵒ.ℐ.∘ t) Sᵒ.∘ h}
                           (QUCᵒ.sub-merge {s = s} {t = t} {g = h}))))

-- Serial composition, `Abstract2.UC-compose` at a slack.
constructs-∙ : {f : A Sᵒ.⇒ Sᵒ.T₀ X B} {g : A Sᵒ.⇒ Sᵒ.T₀ Y B}
               {u : B Sᵒ.⇒ Sᵒ.T₀ P C} {v : B Sᵒ.⇒ Sᵒ.T₀ R C}
             → Constructs ε f g → Constructs ε′ u v → Constructs (ε′ ℚ.+ ε) (u Sᵒ.∙ f) (v Sᵒ.∙ g)
constructs-∙ {ε = ε} {ε′ = ε′} {f = f} {g = g} {u = u} {v = v} cf cu =
  let s , hf = Constructs⇒Witness⁺ {ε = ε} {f = f} {g = g} cf
      t , hu = Constructs⇒Witness⁺ {ε = ε′} {f = u} {g = v} cu
  in Witness⁺⇒Constructs {ε = ε′ ℚ.+ ε} {f = u Sᵒ.∙ f} {g = v Sᵒ.∙ g}
       ( (Sᵒ.ℐ.id Sᵒ.ℐ.⊗₁ t) Sᵒ.ℐ.∘ (s Sᵒ.ℐ.⊗₁ Sᵒ.ℐ.id)
       , λ δ pos → QUCᵒ.ctx-mono {f = u Sᵒ.∙ f}
                     {g = Sᵒ.sub ((Sᵒ.ℐ.id Sᵒ.ℐ.⊗₁ t) Sᵒ.ℐ.∘ (s Sᵒ.ℐ.⊗₁ Sᵒ.ℐ.id)) Sᵒ.∘ (v Sᵒ.∙ g)}
                     (≤-reflexive (½-split ε′ ε δ))
                     (QUCᵒ.at-compose {εf = ε ℚ.+ ½ ℚ.* δ} {εu = ε′ ℚ.+ ½ ℚ.* δ}
                                      {s = s} {t = t} {f = f} {g = g} {u = u} {v = v}
                                      (hf (½ ℚ.* δ) (0<½* pos)) (hu (½ ℚ.* δ) (0<½* pos))))
