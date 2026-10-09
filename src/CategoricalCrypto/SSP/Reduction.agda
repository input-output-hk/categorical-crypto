{-# OPTIONS --safe --without-K #-}

-- SSP's reasoning principles in the setup (brzuska2018 §2.3).  `G₀ ≈ᵍ[ ε ] G₁`
-- bounds every distinguisher at ε (Def. 8 at a scalar ε); the triangle
-- inequality (Lemma 5) is `≈[]-trans` of the two-sided readout, and the
-- reduction lemma (Lemma 6) moves a package from the game into the
-- distinguisher — the associativity simulation, read out.
--
-- `closed-bridge`: between CLOSED protocols `unit ⇒ T₀ X B`, game equivalence
-- is already the U-kernel, with no `GradeStable` (`docs/uc-setup-ssp.md` §5.1).
-- An ancilla closure `m : unit ⇒ Y ⊗ unit` slides past the closed protocol by
-- naturality, interchange and `λ⇐ = ρ⇐` at the unit, which leaves one test of
-- the protocol alone.

open import Categories.Category.Monoidal.Bundle

open import Data.Rational using (ℚ; _+_)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid using (module Mℚ)

open import CategoricalCrypto.Approx.Error using (Approximation; ≈[]-resp₀; ℚ-ordered)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.SSP.Protocol.Monoidal using (Protᴹ)
import CategoricalCrypto.SSP.Setup as Setup

module CategoricalCrypto.SSP.Reduction where

open Approximation Approximation⊥ using (_≈[_]_; ≈[]-trans)

private variable
  A B C X : Iface
  ε δ : ℚ

------------------------------------------------------------------------
-- Games at a measured advantage

infix 4 _≈ᵍ[_]_

_≈ᵍ[_]_ : Protocol unitᴵ A → ℚ → Protocol unitᴵ A → Set₁
_≈ᵍ[_]_ {A} G₀ ε G₁ = (D : Protocol A Ωᴵ) → runᵖ (D ∘ᵖ G₀) ≈[ ε ] runᵖ (D ∘ᵖ G₁)

-- Lemma 5.
≈ᵍ-trans : {G₀ G₁ G₂ : Protocol unitᴵ A} → G₀ ≈ᵍ[ ε ] G₁ → G₁ ≈ᵍ[ δ ] G₂ → G₀ ≈ᵍ[ ε + δ ] G₂
≈ᵍ-trans {G₀ = G₀} {G₁} {G₂} h k D =
  ≈[]-trans {runᵖ (D ∘ᵖ G₀)} {runᵖ (D ∘ᵖ G₁)} {runᵖ (D ∘ᵖ G₂)} (h D) (k D)

-- Lemma 6.
reduction : (D : Protocol B Ωᴵ) (M : Protocol A B) (G : Protocol unitᴵ A)
          → runᵖ ((D ∘ᵖ M) ∘ᵖ G) ≈Mℚ runᵖ (D ∘ᵖ (M ∘ᵖ G))
reduction D M G = runᵖ-sim (∘ᵖ-assoc D M G)

-- …so a package on top of two close games keeps them as close.
≈ᵍ-reduce : (M : Protocol A B) {G₀ G₁ : Protocol unitᴵ A}
          → G₀ ≈ᵍ[ ε ] G₁ → M ∘ᵖ G₀ ≈ᵍ[ ε ] M ∘ᵖ G₁
≈ᵍ-reduce M {G₀} {G₁} h D = ≈[]-resp₀ ℚ-ordered Approximation⊥
  {x = runᵖ ((D ∘ᵖ M) ∘ᵖ G₀)} {runᵖ (D ∘ᵖ (M ∘ᵖ G₀))} {runᵖ ((D ∘ᵖ M) ∘ᵖ G₁)} {runᵖ (D ∘ᵖ (M ∘ᵖ G₁))}
  (≈Mℚ⇒≈[0] {runᵖ (D ∘ᵖ (M ∘ᵖ G₀))} {runᵖ ((D ∘ᵖ M) ∘ᵖ G₀)}
            (Mℚ.sym {x = runᵖ ((D ∘ᵖ M) ∘ᵖ G₀)} {y = runᵖ (D ∘ᵖ (M ∘ᵖ G₀))} (reduction D M G₀)))
  (≈Mℚ⇒≈[0] {runᵖ ((D ∘ᵖ M) ∘ᵖ G₁)} {runᵖ (D ∘ᵖ (M ∘ᵖ G₁))} (reduction D M G₁))
  (h (D ∘ᵖ M))

------------------------------------------------------------------------
-- The bridge at closed protocols

-- Proved in an arbitrary monoidal category: at `Protᴹ` every implicit
-- morphism of a reasoning step would be solved through the transparent
-- `_∘ᵖ_`, i.e. as a protocol record.
private
  module Closed {o ℓ e} (𝕄 : MonoidalCategory o ℓ e) where
    open MonoidalCategory 𝕄
    open import Categories.Category.Monoidal.Properties monoidal using (coherence-inv₃)
    open import Categories.Category.Monoidal.Reasoning monoidal
    import Categories.Category.Monoidal.Utilities monoidal as Util
    open import Categories.Morphism.Reasoning U
    open Util.Shorthands

    slide : {W Y : Obj} (h : unit ⇒ W) (m : unit ⇒ Y ⊗₀ unit)
          → id ⊗₁ h ∘ m ≈ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐ ∘ h
    slide h m = begin
      id ⊗₁ h ∘ m                      ≈⟨ refl⟩∘⟨ introˡ unitorʳ.isoˡ ⟩
      id ⊗₁ h ∘ (ρ⇐ ∘ ρ⇒) ∘ m          ≈⟨ refl⟩∘⟨ assoc ⟩
      id ⊗₁ h ∘ ρ⇐ ∘ ρ⇒ ∘ m            ≈⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
      id ⊗₁ h ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ ρ⇐    ≈⟨ pullˡ (⟺ serialize₂₁) ⟩
      (ρ⇒ ∘ m) ⊗₁ h ∘ ρ⇐               ≈⟨ pushˡ serialize₁₂ ⟩
      (ρ⇒ ∘ m) ⊗₁ id ∘ id ⊗₁ h ∘ ρ⇐    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ coherence-inv₃ ⟩
      (ρ⇒ ∘ m) ⊗₁ id ∘ id ⊗₁ h ∘ λ⇐    ≈⟨ refl⟩∘⟨ ⟺ unitorˡ-commute-to ⟩
      (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐ ∘ h          ∎

    close : {X B Y Z : Obj} (h : unit ⇒ X ⊗₀ B) (t : (Y ⊗₀ X) ⊗₀ B ⇒ Z) (m : unit ⇒ Y ⊗₀ unit)
          → ((t ∘ α⇐ ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐) ∘ h) ∘ id ≈ (t ∘ α⇐ ∘ id ⊗₁ h) ∘ m
    close h t m = begin
      ((t ∘ α⇐ ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐) ∘ h) ∘ id  ≈⟨ identityʳ ⟩
      (t ∘ α⇐ ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐) ∘ h         ≈⟨ assoc²βε ⟩
      t ∘ α⇐ ∘ ((ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐) ∘ h         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      t ∘ α⇐ ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐ ∘ h           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (slide h m) ⟩
      t ∘ α⇐ ∘ id ⊗₁ h ∘ m                       ≈⟨ assoc²βε ⟨
      (t ∘ α⇐ ∘ id ⊗₁ h) ∘ m                     ∎

open Setup

closed-bridge : {f g : unit ⇒ T₀ X B} → f ≈ℰ g → f ≈ᵁ g
closed-bridge {X} {B} {f} {g} e Y = KE.mk∼ λ {t} m →
  read-cast (Closed.close Protᴹ {X} {B} {Y} {Ω} f t m) (Closed.close Protᴹ {X} {B} {Y} {Ω} g t m)
            (KE.run∼ e {t ∘ α⇐ ∘ (ρ⇒ ∘ m) ⊗₁ id ∘ λ⇐} id)
