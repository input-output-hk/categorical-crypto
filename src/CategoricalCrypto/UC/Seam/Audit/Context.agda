{-# OPTIONS --safe --without-K --guardedness #-}

-- The certified context a strategy's closed run is read at: the embedded
-- strategy behind two unitors at the trivial grade, with a unitor closure.

import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.LocallyGraded.SubCategory
import Categories.Morphism.Reasoning as MR

open import Data.Nat.Positive
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy
open import CategoricalCrypto.UC.Seam.Budget
open import CategoricalCrypto.UC.Seam.Grounded

module CategoricalCrypto.UC.Seam.Audit.Context where

open MonR monoidal
open GradedSubCat gradingᵒ
open MR ∣machines∣

auditClose : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ 𝟘ᵒ
auditClose = ιᴳ unitᴵ

module _ (B : Iface) (e : Strat (Neg B) (Pos B)) where

  private
    env : Proc B Ωᴵ
    env = strategyEnv B e

    test : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
    test = procᵒ env ∘ unitorˡ.from

  auditTest : T₀ 𝟘ᴳ (T₀ 𝟘ᴳ (ifaceᵒ B)) ⇒ Ωᵒ
  auditTest = test ∘ unitorˡ.from

  audit-qb : (q : ℕ⁺) → asks≤ (value q) e → Pred q auditTest
  audit-qb q a =
    pred-sub (ℕP.≤-reflexive (trans (ℕP.*-identityˡ _) (ℕP.*-identityˡ (value q))))
      (pred-∘ (pred-∘ (qbᵒ {r = q} (qb-strategyEnv B (value q) e a)) pred-λ⇒) pred-λ⇒)

  audit-run : (w : Proc unitᴵ B)
            → observe (auditTest ∘ id ⊗₁ closedᵒ w) auditClose ≈ₚ runᴹ w e
  audit-run w =
    ≈ₚ-trans _ _ _ (obs-resp (plug-λ test (closedᵒ w) ○ cancelInner unitorˡ.isoʳ))
      (≈ₚ-trans _ _ _ (≈ₚ-sym _ _ (plug-run B e w)) (adequacy B w e))
