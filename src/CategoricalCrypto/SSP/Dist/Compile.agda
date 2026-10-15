{-# OPTIONS --safe --without-K --guardedness #-}

-- The existing SSP compiler descends through distributional equality to PM[wb].
-- See docs/uc-setup-ssp-dist.md §6 for the security and observation boundary.

module CategoricalCrypto.SSP.Dist.Compile where

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Data.Product.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Bundles
import Categories.Morphism as Mor

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Semantics
import CategoricalCrypto.Standard2.Coverage as Coverage
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UCSetup.Coverage
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.SSP.Dense as Dense
import CategoricalCrypto.SSP.Dense.Tests as Tests
import CategoricalCrypto.SSP.Dist.Setup as SSPᵈ
import CategoricalCrypto.SSP.Setup as SSP
import CategoricalCrypto.UC.Bracket.Setup as WB

private variable A B X Y Z : Iface

compile-pad : (P : Protocol A B)
            → ⟦ (wireᵖ {Y} ⊗ᵖ P) ⊗ᵖ wireᵖ {Z} ⟧ᵂ WB.≈ WB.pad {Y} {Z = Z} ⟦ P ⟧ᵂ
compile-pad {Y = Y} {Z = Z} P =
  ⊗≈⊗ (wireᵖ {Y} ⊗ᵖ P) (wireᵖ {Z})
  ○ WB.⊗.F-resp-≈ ((⊗≈⊗ (wireᵖ {Y}) P ○ WB.⊗.F-resp-≈ (wire≈σ , WB.Equiv.refl)) , wire≈σ)
  where open WB.HomReasoning

⟦⟧ᵂ-resp-≈ᵈ : {P Q : Protocol A B} → P ≈ᵈ Q → ⟦ P ⟧ᵂ WB.≈ ⟦ Q ⟧ᵂ
⟦⟧ᵂ-resp-≈ᵈ {A} {B} {P} {Q} e Y Z = WB.𝒲ᵂ.KE.mk∼ λ {t} →
  WB.KE.run∼ (padded Y Z) {t}
  where
  padded : (Y Z : Iface) → WB.pad {Y} {Z = Z} ⟦ P ⟧ᵂ WB.≈ℰ WB.pad ⟦ Q ⟧ᵂ
  padded Y Z = WB.≈ℰ-trans (WB.≈C⇒≈ℰ (WB.Equiv.sym (compile-pad {Y = Y} {Z = Z} P)))
    (WB.≈ℰ-trans (Tests.preserves-≈ℰ (run≈ᵈ e Y Z)) (WB.≈C⇒≈ℰ (compile-pad {Y = Y} {Z = Z} Q)))

Fᵂᵈ : StrongMonoidalFunctor SSPᵈ.Protᵈ WB.PM[wb]ᴹ
Fᵂᵈ = record
  { F = record
    { F₀ = λ A → A ; F₁ = ⟦_⟧ᵂ
    ; identity = F.identity ; homomorphism = F.homomorphism
    ; F-resp-≈ = ⟦⟧ᵂ-resp-≈ᵈ }
  ; isStrongMonoidal = record
    { ε = F.ε
    ; ⊗-homo = niHelper record
      { η = F.⊗-homo.⇒.η ; η⁻¹ = F.⊗-homo.⇐.η ; commute = F.⊗-homo.⇒.commute
      ; iso = λ XY → record
        { isoˡ = F.⊗-homo.iso.isoˡ XY ; isoʳ = F.⊗-homo.iso.isoʳ XY } }
    ; associativity = F.associativity ; unitaryˡ = F.unitaryˡ ; unitaryʳ = F.unitaryʳ } }
  where module F = StrongMonoidalFunctor Fᵂ

νᵂᵈ : PresheafMorphism (StrongMonoidalFunctor.F Fᵂᵈ) SSPᵈ.ℰᵈ WB.ℰ[wb]
νᵂᵈ = record { ν = ntHelper record { η = νᵂ.η ; commute = νᵂ.commute } }
  where module νᵂ = PresheafMorphism Dense.νᵂ

dist⇒PM[wb] : UCSetupMorphism SSPᵈ.StdSetup WB.StdSetup
dist⇒PM[wb] = StdUCMorphism SSPᵈ.Protᵈ WB.PM[wb]ᴹ SSPᵈ.ℰᵈ WB.ℰ[wb] Fᵂᵈ νᵂᵈ

module Coverageᵈ = Coverage.Coverage SSPᵈ.Protᵈ WB.PM[wb]ᴹ SSPᵈ.ℰᵈ WB.ℰ[wb] Fᵂᵈ νᵂᵈ

test-coverage : TestCoverage dist⇒PM[wb]
test-coverage = record { complete = λ {A} {B} {h} {k} →
  TestCoverage.complete Tests.test-coverage {A} {B} {h} {k} }

ancilla-coverage : Coverageᵈ.AncillaCoverage
ancilla-coverage = Coverageᵈ.essentiallySurjective⇒AncillaCoverage
  (λ A → A , Mor.≅.refl (MonoidalCategory.U WB.PM[wb]ᴹ))

preserves-≈ℰ : Transfer.Preserves-≈ℰ dist⇒PM[wb]
preserves-≈ℰ = covered-≈ℰ dist⇒PM[wb] test-coverage

preserves-≈ᵁ : Transfer.Preserves-≈ᵁ dist⇒PM[wb]
preserves-≈ᵁ = Coverageᵈ.covered-≈ᵁ test-coverage ancilla-coverage

preserves-≤UC : Transfer.Preserves-≤UC dist⇒PM[wb]
preserves-≤UC = Coverageᵈ.covered-≤UC test-coverage ancilla-coverage

------------------------------------------------------------------------
-- Pointwise agreement of the actual composed setup morphisms
------------------------------------------------------------------------

ssp-via-dist : UCSetupMorphism SSP.StdSetup WB.StdSetup
ssp-via-dist = composeᵁ dist⇒PM[wb] SSPᵈ.ssp⇒dist

module Triangle where
  module Via = UCSetupMorphism ssp-via-dist
  module Direct = UCSetupMorphism Dense.SSP→PM[wb]

  objects : (A : Iface) → Via.F.₀ A ≡ Direct.F.₀ A
  objects A = refl

  homs : (P : Protocol A B) → Via.F.₁ P WB.≈ Direct.F.₁ P
  homs P = WB.Equiv.refl

  tests : (D : Protocol A Ωᴵ)
        → Setoid._≈_ (Functor.₀ WB.ℰ[wb] A) (Via.ν.η A ⟨$⟩ D) (Direct.ν.η A ⟨$⟩ D)
  tests {A} D = Setoid.refl (Functor.₀ WB.ℰ[wb] A) {Via.ν.η A ⟨$⟩ D}

  grade-objects : (X : Iface) → Via.Φ.₀ X ≡ Direct.Φ.₀ X
  grade-objects X = refl

  grade-homs : (s : Protocol X Y) → Via.Φ.₁ s WB.≈ Direct.Φ.₁ s
  grade-homs s = WB.Equiv.refl

  κ : Via.κ {X} {A} WB.≈ Direct.κ {X} {A}
  κ = WB.identityˡ ○ wire≈σ
    where open WB.HomReasoning

  tensor : Via.Φ.⊗-homo.η (X , Y) WB.≈ Direct.Φ.⊗-homo.η (X , Y)
  tensor = WB.identityʳ ○ wire≈σ
    where open WB.HomReasoning

  unit : Via.Φ.ε WB.≈ Direct.Φ.ε
  unit = WB.identityʳ ○ wire≈σ
    where open WB.HomReasoning

  computations : (f : Protocol A (X ⊗ᴵ B))
               → Transfer.G ssp-via-dist f WB.≈ Transfer.G Dense.SSP→PM[wb] f
  computations f = WB.∘-resp-≈ κ (homs f)

  return-comparison : WB.sub Via.Φ.ε WB.∘ WB.return {A}
                      WB.≈ WB.sub Direct.Φ.ε WB.∘ WB.return {A}
  return-comparison = WB.Equiv.sym Via.κ-return
    ○ computations SSP.return ○ Direct.κ-return
    where open WB.HomReasoning

  ext-comparison : (f : Protocol A (Y ⊗ᴵ B))
    → WB.sub (Via.Φ.⊗-homo.η (X , Y))
        WB.∘ WB.ext (Via.Φ.₀ X) (Transfer.G ssp-via-dist f) WB.∘ Via.κ
      WB.≈ WB.sub (Direct.Φ.⊗-homo.η (X , Y))
        WB.∘ WB.ext (Direct.Φ.₀ X) (Transfer.G Dense.SSP→PM[wb] f) WB.∘ Direct.κ
  ext-comparison {X = X} f = WB.Equiv.sym (Via.κ-ext f)
    ○ computations (SSP.ext X f) ○ Direct.κ-ext f
    where open WB.HomReasoning

  sub-comparison : (s : Protocol X Y)
    → WB.sub (Via.Φ.₁ s) WB.∘ Via.κ {X} {A}
      WB.≈ WB.sub (Direct.Φ.₁ s) WB.∘ Direct.κ {X} {A}
  sub-comparison s = WB.Equiv.sym (Via.κ-sub s)
    ○ computations (SSP.sub s) ○ Direct.κ-sub s
    where open WB.HomReasoning
