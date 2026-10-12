{-# OPTIONS --safe --without-K --guardedness #-}

-- Restriction from full PM observations to well-bracketed observations on
-- the same machines. The verdict interface has one channel, so a test needs
-- no monitor: every output following a legal input is already a legal move.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Bracket.Setup
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

import Data.Unit.Base as Unit
import CategoricalCrypto.Iface as Flat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Bracket.ObservationRestriction where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module G = MonoidalCategory 𝔾ᵒ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module Oᵂ = Observable (Evaluation.observable evaluationᵂ)

private variable
  A B X Y : Iface

verdict-W : (t : Proc (flat A) (flat Ωᴵ)) → W {A} {Ωᴵ} t
verdict-W {A} t = record
  { I = I
  ; I-init = λ n → Supp-all _ (λ _ → tt) n _
  ; I-step = step-W
  }
  where
  I : MC.St t → Phase A Ωᴵ → Set
  I _ _ = ⊤

  legal : {b : Ch Ωᴵ} → (y : MC.St t × (Σ (Ch A) (Q A) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ))) → Legal I (serving b) y
  legal {Unit.tt} (_ , inj₁ (a , q)) = calling Unit.tt a , call , tt
  legal {Unit.tt} (_ , inj₂ (Unit.tt , r)) = idle , answer , tt

  step-W : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n
         → Supp n (MC.step t (s , x)) (Legal I φ′)
  step-W _ query n = Supp-all _ legal n _
  step-W _ return n = Supp-all _ legal n _

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ unprocᵒ

  verdict-Wᵒ : (t : Uᵂ A G.⇒ Uᵂ Ωᴵ) → Wᵒ {A} {Ωᴵ} t
  verdict-Wᵒ t = unprocᵒ t , verdict-W (unprocᵒ t) , G.Equiv.refl

ωʷ⁻¹ : Proc (Bool Flat.⇿ Unit.⊤) (flat Ωᴵ)
ωʷ⁻¹ = wireᴹ (Unit.tt ,_) proj₂

opaque
  ωʷ-inverseˡ : procᵒ ωʷ G.∘ procᵒ ωʷ⁻¹ G.≈ G.id
  ωʷ-inverseˡ =
      G.Equiv.sym (procᵒ-∘ ωʷ ωʷ⁻¹)
    ○ ≈ᴹ⇒≈ᵒ (wire∘wire {B = flat Ωᴵ} {C = Bool Flat.⇿ Unit.⊤} {A = Bool Flat.⇿ Unit.⊤}
                 proj₂ (λ _ → Unit.tt , Unit.tt) (Unit.tt ,_) proj₂
       S.○ᴹ wire-cong (λ _ → refl) (λ { Unit.tt → refl }) S.○ᴹ wire-id)
    ○ G.Equiv.sym procᵒ-id
    where open G.HomReasoning

  ωʷ-inverseʳ : procᵒ ωʷ⁻¹ G.∘ procᵒ ωʷ G.≈ G.id
  ωʷ-inverseʳ =
      G.Equiv.sym (procᵒ-∘ ωʷ⁻¹ ωʷ)
    ○ ≈ᴹ⇒≈ᵒ (wire∘wire {B = Bool Flat.⇿ Unit.⊤} {C = flat Ωᴵ} {A = flat Ωᴵ}
                 (Unit.tt ,_) proj₂ proj₂ (λ _ → Unit.tt , Unit.tt)
       S.○ᴹ wire-cong (λ { (Unit.tt , _) → refl }) (λ { (Unit.tt , Unit.tt) → refl })
       S.○ᴹ wire-id)
    ○ G.Equiv.sym procᵒ-id
    where open G.HomReasoning

module Full = Std2.StdUC 𝒲ᴹ ι*ℰᵒ

FullTest : Iface → Set (suc 0ℓ)
FullTest A = Setoid.Carrier (Functor.₀ ι*ℰᵒ A)

restrict-test : FullTest A → A 𝒲ᵂ.⇒ Ωᴵ
restrict-test t = h , verdict-Wᵒ h
  where h = procᵒ ωʷ⁻¹ G.∘ t

-- This chooses a full-test representative; it does not transport the coarser
-- equality of well-bracketed tests back to equality under hostile closures.
full-test : A 𝒲ᵂ.⇒ Ωᴵ → FullTest A
full-test t = procᵒ ωʷ G.∘ proj₁ t

restrict-read : (t : FullTest A) (c : unitᴵ 𝒲ᵂ.⇒ A)
              → Obsᵂ (restrict-test t 𝒲ᵂ.∘ c) ≈ₚ Obs (t G.∘ (proj₁ c G.∘ procᵒ υʷ))
restrict-read t c = obs-resp
  ((refl⟩∘⟨ (G.assoc ○ G.assoc)) ○ G.sym-assoc ○ (ωʷ-inverseˡ ⟩∘⟨refl) ○ G.identityˡ)
  where open G.HomReasoning

restrict-cong : {t u : FullTest A} → Setoid._≈_ (Functor.₀ ι*ℰᵒ A) t u
              → Oᵂ._≋_ {A = A} (restrict-test {A} t) (restrict-test {A} u)
restrict-cong {A} {t} {u} e c =
  ∼ᴼ-resp (≈sym (restrict-read t c)) (≈sym (restrict-read u c)) (e (proj₁ c G.∘ procᵒ υʷ))

restrict-natural : (f : B 𝒲ᵂ.⇒ A) (t : FullTest A)
                 → Oᵂ._≋_ {A = B} (restrict-test {B} (t G.∘ proj₁ f)) (restrict-test {A} t 𝒲ᵂ.∘ f)
restrict-natural {B} {A} f t = Oᵂ.≈⇒≋ {A = B}
  {t = restrict-test {B} (t G.∘ proj₁ f)} {u = restrict-test {A} t 𝒲ᵂ.∘ f} G.sym-assoc

ν-restrict : PresheafMorphism idF ι*ℰᵒ ℰᵂ
ν-restrict = record { ν = ntHelper record
  { η = λ A → record { to = restrict-test {A} ; cong = restrict-cong {A} }
  ; commute = λ {_} {B} f {t} → restrict-natural {B} f t } }

restrict-surjective : (t : A 𝒲ᵂ.⇒ Ωᴵ) → Oᵂ._≋_ {A = A} (restrict-test {A} (full-test t)) t
restrict-surjective {A} t = Oᵂ.≈⇒≋ {A = A} {t = restrict-test {A} (full-test t)} {u = t}
  (G.sym-assoc ○ (ωʷ-inverseʳ ⟩∘⟨refl) ○ G.identityˡ)
  where open G.HomReasoning

ν-restrict-epi : PresheafMorphism.Epi ν-restrict
ν-restrict-epi t = full-test t , restrict-surjective t

restriction⇒wb : UCSetupMorphism Full.StdSetup 𝒲ᵂ.StdSetup
restriction⇒wb = changeKernel ι*ℰᵒ ℰᵂ ν-restrict

full⇒PM[wb] : UCSetupMorphism Full.StdSetup StdSetup
full⇒PM[wb] = composeᵁ q restriction⇒wb
