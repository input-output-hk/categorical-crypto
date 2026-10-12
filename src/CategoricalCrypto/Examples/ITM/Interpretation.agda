{-# OPTIONS --safe --without-K --guardedness #-}

-- Keep the seal's representation proof separate from StdUC record conversion.

module CategoricalCrypto.Examples.ITM.Interpretation where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor.Monoidal

open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Examples.ITM.Tables
open import CategoricalCrypto.Iface
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Functor
open import CategoricalCrypto.ITM.Run
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy

private
  module T = FreeMonoidal itmData
  module F = StrongMonoidalFunctor Fᴾ
  module G = MonoidalCategory 𝔾ᵒ
  module 𝒫 = Category 𝒫ᴵ

real ideal simulated : T.HomTerm T.unit (Service T.⊗₀ Service)
real = T.var (resource true)
ideal = T.var (resource false)
simulated = (T.var simulator T.⊗₁ T.id) T.∘ ideal

resourceTest : Strat (Neg ⟦ Service T.⊗₀ Service ⟧) (Pos ⟦ Service T.⊗₀ Service ⟧)
             → F.₀ (Service T.⊗₀ Service) G.⇒ Ωᵒ
resourceTest d = subst (λ X → X G.⇒ Ωᵒ) (sym (F₀≡ (Service T.⊗₀ Service)))
  (procᵒ (strategyEnv ⟦ Service T.⊗₀ Service ⟧ d))

probeTest : Bool → F.₀ (Service T.⊗₀ Service) G.⇒ Ωᵒ
probeTest honest = resourceTest (probe honest)

emptyClosure : 𝟘ᵒ G.⇒ F.₀ T.unit
emptyClosure = subst (λ X → 𝟘ᵒ G.⇒ X) (sym (F₀≡ T.unit)) (procᵒ emptyᴹ)

observation : Bool → T.HomTerm T.unit (Service T.⊗₀ Service) → Dₚ Bool
observation honest f = Obs ((probeTest honest G.∘ F.₁ f) G.∘ emptyClosure)

opaque
  unfolding 𝔾ᵒ procᵒ unitᵒ ⊗ᵒ

  compiled-correct : F.₁ simulated G.≈ F.₁ real
  compiled-correct = G.Equiv.trans
    (G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ {A = ⟦ Service ⟧} (runᴾ {Service} {Service} simulator)))) tables-correct

  observe-resource : (marker : Bool)
                     (d : Strat (Neg ⟦ Service T.⊗₀ Service ⟧) (Pos ⟦ Service T.⊗₀ Service ⟧))
                   → Obs ((resourceTest d G.∘ F.₁ (T.var {T.unit} {Service T.⊗₀ Service} (resource marker))) G.∘ emptyClosure)
                     ≈ₚ runᴹ (closed-resource marker) d
  observe-resource marker d = obs-resp
    (G.assoc {A = 𝟘ᵒ} {B = F.₀ T.unit} {C = F.₀ (Service T.⊗₀ Service)} {D = Ωᵒ}
      {f = emptyClosure} {g = F.₁ (T.var {T.unit} {Service T.⊗₀ Service} (resource marker))} {h = resourceTest d})
    ⟨≈⟩ obs-resp (≈ᴹ⇒≈ᵒ (𝒫.∘-resp-≈ʳ {unitᴵ} {⟦ Service T.⊗₀ Service ⟧} {Ωᴵ}
      {f = runᴾ {T.unit} {Service T.⊗₀ Service} (resource marker) 𝒫.∘ emptyᴹ}
      {h = closed-resource marker}
      {g = strategyEnv ⟦ Service T.⊗₀ Service ⟧ d} (closed-correct marker)))
    ⟨≈⟩ adequacy ⟦ Service T.⊗₀ Service ⟧ (closed-resource marker) d

probe-correct : (marker honest : Bool)
              → observation honest (T.var (resource marker)) ≈ₚ runᴹ (closed-resource marker) (probe honest)
probe-correct marker honest = observe-resource marker (probe honest)

real-marker : observation false real ≈ₚ returnₚ true
real-marker = probe-correct true false ⟨≈⟩ probe-grade true

ideal-marker : observation false ideal ≈ₚ returnₚ false
ideal-marker = probe-correct false false ⟨≈⟩ probe-grade false

simulated-marker : observation false simulated ≈ₚ returnₚ true
simulated-marker = obs-resp (G.∘-resp-≈ˡ (G.∘-resp-≈ʳ compiled-correct)) ⟨≈⟩ real-marker

honest-coin : (marker : Bool) → observation true (T.var (resource marker)) ≈ₚ coinₚ uniform-Bool
honest-coin marker = probe-correct marker true ⟨≈⟩ probe-honest marker

honest-independent : (marker : Bool)
                    → Obs ((resourceTest double-probe G.∘ F.₁ (T.var {T.unit} {Service T.⊗₀ Service} (resource marker))) G.∘ emptyClosure)
                      ≈ₚ (coinₚ uniform-Bool >>=ₚ λ b → coinₚ uniform-Bool >>=ₚ λ b′ → returnₚ (if b then b′ else not b′))
honest-independent marker = observe-resource marker double-probe ⟨≈⟩ probe-double marker
