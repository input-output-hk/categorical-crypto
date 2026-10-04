{-# OPTIONS --safe --without-K --guardedness #-}

-- The family UC premise on protocol images, with its error KEPT: `_≈ᶠᴺ_`.
-- `≤UC[]⇒≤UCᴺ` carries a fixed-data bound into the canonical negligible order
-- (`UC.Family.Canonicalᴺ`), which keeps the certified simulator
-- but not the schedule: a caller that needs the number keeps the bound's data.

import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.LocallyGraded.SubCategory
import Categories.Morphism.Reasoning as MR

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy
open import CategoricalCrypto.UC.Seam.Budget

import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Model.Family.Emulation where

private module Cᴺ = Canonicalᴺ

open GradedSubCat gradingᵒ

Systems : (ℕ → Iface) → Set₁
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

private variable B : ℕ → Iface
                 R I : Systems B

------------------------------------------------------------------------
-- The images and the ε-approximate family agreement

gradedᶠ : (B : ℕ → Iface) → Obj^ω
gradedᶠ B = Δ Gr.𝟘ᴳ ⊛ω ifaceᶠ B

imgᶠ : (B : ℕ → Iface) (R : Systems B) (n : ℕ) → 𝟘ᵒ ⇒ gradedᶠ B n
imgᶠ B R n = Gr.stageᵒ (morphism (R n))

infix 4 _≈ᶠ[_]_

_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁
_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctx[ ε ] imgᶠ B I

infix 4 _≈ᶠᴺ_

-- Symmetric and simulator-free; the simulator-bearing relation is
-- `UC.Quantitative.Family._≤UC^ωᵉ_`.
_≈ᶠᴺ_ : Systems B → Systems B → Set₁
R ≈ᶠᴺ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I

------------------------------------------------------------------------
-- The witness form, and the `_≈ℰⁿ_` tier it lands in

-- `ε` is EXPLICIT here and in `≈ᶠ-runs`, for `UC.Approximate.NegligibleBound-+`'s
-- reason.  An implication, not an identification: `_≈ℰ[_]_` quantifies over
-- levelwise FAMILIES of contexts carrying one polynomial, where the contextual
-- relation quantifies each level's context separately.
≈ctx⇒≈ℰ[] : {A X B : Obj^ω} (ε : ℕ → ℕ → ℚ) (f g : A ⇒^ω (X ⊛ω B))
          → sim f ≈ctx[ ε ] sim g → _≈ℰ[_]_ f ε g
≈ctx⇒≈ℰ[] _ _ _ h Y Et m _ cE n =
  h n (Y n) ⌊ hom Et n ⌋ ⌊ hom m n ⌋ (cE n) (hom m n , Equiv.refl)

module _ {A X Y B : Obj^ω} (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ)
         (neg : NegligibleBound ε) (f : A ⇒^ω (X ⊛ω B)) (g : A ⇒^ω (Y ⊛ω B))
         (e : sim f ≤UC[ s , ε ] sim g) where

  ≤UC[]⇒≈ℰⁿ : _≈ℰⁿ_ {A} f (Cᴺ.sub s Cᴺ.∘ g)
  ≤UC[]⇒≈ℰⁿ = ε , carried-negligible {ε = ε} neg
            , ≈ctx⇒≈ℰ[] ε f (Cᴺ.sub s Cᴺ.∘ g) e

  ≤UC[]⇒≤UCᴺ : f Cᴺ.≤UC g
  ≤UC[]⇒≤UCᴺ = Cᴺ.dummy-complete {f = f} {g = g} (s , ≈ℰⁿ⇒≈ℰᴺ f (Cᴺ.sub s Cᴺ.∘ g) ≤UC[]⇒≈ℰⁿ)

-- The context a strategy's closed run is read at: the embedded strategy behind
-- the two unitors at the trivial grade, at its own ask-depth, closed by the
-- unitor `Gr.ιᴳ unitᴵ`.
module _ (B : Iface) (e : Strat (Neg B) (Pos B)) where

  open Gr
  open MonR monoidal
  open MR ∣machines∣

  private
    test : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
    test = procᵒ (strategyEnv B e) ∘ unitorˡ.from

  auditTest : T₀ 𝟘ᴳ (T₀ 𝟘ᴳ (ifaceᵒ B)) ⇒ Ωᵒ
  auditTest = test ∘ unitorˡ.from

  audit-qb : (q : ℕ⁺) → asks≤ (value q) e → Pred q auditTest
  audit-qb q a =
    pred-sub (≤-reflexive (trans (*-identityˡ _) (*-identityˡ (value q))))
      (pred-∘ (pred-∘ (qbᵒ {r = q} (qb-strategyEnv B (value q) e a)) pred-λ⇒) pred-λ⇒)

  audit-run : (w : Proc unitᴵ B)
            → observe (auditTest ∘ id ⊗₁ stageᵒ w) (ιᴳ unitᴵ) ≈ₚ runᴹ w e
  audit-run w =
    ≈ₚ-trans _ _ _ (obs-resp (plug-λ test (stageᵒ w) ○ cancelInner unitorˡ.isoʳ))
      (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B e w)) (adequacy B w e))

-- At a unitor closure at `1⁺` (hence `*-identityʳ`), the premise's `ε` lands
-- on the DIRECT runs.
≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I
        → (n : ℕ) (q : ℕ⁺) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (value q) d
        → runᴹ (morphism (R n)) d ≈ₚ[ ε n (value q) ] runᴹ (morphism (I n)) d
≈ᶠ-runs ε h n q d a =
  subst (λ k → _ ≈ₚ[ ε n k ] _) (*-identityʳ (value q))
        (≈ₚ[]-resp (audit-run _ d _) (audit-run _ d _)
                   (h n Gr.𝟘ᴳ (auditTest _ d) (Gr.ιᴳ unitᴵ)
                      ((auditTest _ d , audit-qb _ d q a) , Equiv.refl)
                      ((Gr.ιᴳ unitᴵ , pred-λ⇐) , Equiv.refl)))
