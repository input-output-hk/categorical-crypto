{-# OPTIONS --safe --without-K --guardedness #-}

-- Maurer's composition theorem at a slack (maurer2002 Lemma 5(ii)–(iii),
-- maurer2011cc Def 2 and Lemma 1): a context a distinguisher can simulate does
-- not increase Δ.  `Absorbs` is that simulation, `♯ d b i` the distinguisher
-- d∘𝒞 cut off at budget i, so Δ^{d∘𝒞} ranges over the cut-offs
-- (`absorbs-Δ`).  Hence G-composition and the tensor are nonexpansive in each
-- argument and add the slacks of both, on raw machines and on the sealed 𝔾ᵒ,
-- where a closing context reads Δ off the observation (`close-∼ᴿ[]`).  See
-- docs/uc-setup-random-systems.md §4.4.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin; zero; suc; inject₁; fromℕ)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Base using (tt)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
import Algebra.Properties.Monoid.Sum as Sum

open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Rational
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Behaviour.Absorb hiding (module Approximation)
open import CategoricalCrypto.UC.Machine.Behaviour.Congruence
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.RandomSystems.Composition where

open Sum +-0-monoid

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ
  variable
    X Y X′ Y′ : Set
    f g : MC.Machine X Y
    ε δ : ℚ

------------------------------------------------------------------------
-- Contexts a distinguisher can simulate

-- Δ^d(𝒞 f, 𝒞 g) ≤ Δ^{d∘𝒞}(f, g)
absorbs-Δ : {C : MC.Machine X Y → MC.Machine X′ Y′} (𝔸 : Absorbs C) (d : Strat X′ Y′)
          → ((b : Bool) (i : Absorbs.Ix 𝔸) → Δ[ Absorbs.♯ 𝔸 d b i ]⟨ f , g ⟩≤ ε)
          → Δ[ d ]⟨ C f , C g ⟩≤ ε
absorbs-Δ {f = f} {g = g} 𝔸 d h = Verdict.slack λ δ pos →
    (λ b → absorbs-dom 𝔸 {f} {g} d b λ i → proj₁ (Verdict.≈̄⇒≈ (h b i) δ pos) b)
  , (λ b → absorbs-dom 𝔸 {g} {f} d b λ i → proj₂ (Verdict.≈̄⇒≈ (h b i) δ pos) b)

absorbs-≈ᴿ[] : {C : MC.Machine X Y → MC.Machine X′ Y′} → Absorbs C → f ≈ᴿ[ ε ] g → C f ≈ᴿ[ ε ] C g
absorbs-≈ᴿ[] 𝔸 e d = absorbs-Δ 𝔸 d λ b i → e (Absorbs.♯ 𝔸 d b i)

-- The hybrid argument with one replacement per step: hybrid i+1 is hybrid i
-- with f turned into g inside a context a distinguisher can simulate.
hybrid-absorbs : {n : ℕ} (H : Fin (suc n) → MC.Machine X′ Y′) (C : Fin n → MC.Machine X Y → MC.Machine X′ Y′)
               → ((i : Fin n) → Absorbs (C i))
               → ((i : Fin n) → H (inject₁ i) ≈ᴿ C i f) → ((i : Fin n) → C i g ≈ᴿ H (suc i))
               → f ≈ᴿ[ ε ] g → H zero ≈ᴿ[ ∑[ i < n ] ε ] H (fromℕ n)
hybrid-absorbs {ε = ε} H C 𝔸 l r e =
  hybrid approxᴿ H (λ _ → ε) λ i → ≈ᴿ[]-resp (l i) (r i) (absorbs-≈ᴿ[] (𝔸 i) e)

------------------------------------------------------------------------
-- The G construction: maurer2002 Lemma 5(iii) for the cascade,
-- maurer2011cc Def 2 (3) for the tensor

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set} where

  composeᴳ-≈ᴿ[] : {f h : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)} {g i : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)}
                → f ≈ᴿ[ ε ] h → g ≈ᴿ[ δ ] i
                → _≈ᴿ[_]_ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} (𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} f g) (ε ℚ.+ δ)
                                                (𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} h i)
  composeᴳ-≈ᴿ[] {h = h} {g = g} e e′ =
    ≈ᴿ[]-trans (absorbs-≈ᴿ[] (∘ᴳ-absorbˡ g) e) (absorbs-≈ᴿ[] (∘ᴳ-absorbʳ h) e′)

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ : Set} where

  ⊗₁ᴳ-≈ᴿ[] : {f h : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {g i : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)}
           → f ≈ᴿ[ ε ] h → g ≈ᴿ[ δ ] i
           → _≈ᴿ[_]_ {(A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)} {(A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺)}
                     (𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g) (ε ℚ.+ δ)
                     (𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} h i)
  ⊗₁ᴳ-≈ᴿ[] {h = h} {g = g} e e′ =
    ≈ᴿ[]-trans (absorbs-≈ᴿ[] (⊗₁ᴳ-absorbˡ g) e) (absorbs-≈ᴿ[] (⊗₁ᴳ-absorbʳ h) e′)

------------------------------------------------------------------------
-- …and on the sealed 𝔾ᵒ

infix 4 _∼ᴿ[_]_

-- `_≈ᴿ[_]_` at 𝔾ᵒ's homs, read through `FullAbstraction.unhomᵒ`.
_∼ᴿ[_]_ : {A B : G.Obj} → A G.⇒ B → ℚ → A G.⇒ B → Set
f ∼ᴿ[ ε ] g = unhomᵒ f ≈ᴿ[ ε ] unhomᵒ g

approxᵒ : {A B : G.Obj} → Approximation (A G.⇒ B) ℚ-ordered 0ℓ
approxᵒ {A} {B} = record
  { _≈[_]_    = _∼ᴿ[_]_
  ; ≈[]-refl  = R.≈[]-refl
  ; ≈[]-sym   = R.≈[]-sym
  ; ≈[]-trans = R.≈[]-trans
  ; ≈[]-mono  = R.≈[]-mono
  }
  where module R = Approximation (approxᴿ {Pos (objᵒ A) ⊎ Neg (objᵒ B)} {Neg (objᵒ A) ⊎ Pos (objᵒ B)})

opaque
  unfolding unhomᵒ

  ∘-resp-∼ᴿ[] : {A B C : G.Obj} {f h : B G.⇒ C} {g i : A G.⇒ B}
              → f ∼ᴿ[ ε ] h → g ∼ᴿ[ δ ] i → (f G.∘ g) ∼ᴿ[ ε ℚ.+ δ ] (h G.∘ i)
  ∘-resp-∼ᴿ[] {ε = ε} {δ} {A} {B} {C} {f} {h} {g} {i} =
    composeᴳ-≈ᴿ[] {proj₁ A} {proj₂ A} {proj₁ B} {proj₂ B} {proj₁ C} {proj₂ C} {ε = ε} {δ = δ}
                  {f = f} {h = h} {g = g} {i = i}

  ⊗-resp-∼ᴿ[] : {A B C D : G.Obj} {f h : A G.⇒ B} {g i : C G.⇒ D}
              → f ∼ᴿ[ ε ] h → g ∼ᴿ[ δ ] i → (f G.⊗₁ g) ∼ᴿ[ ε ℚ.+ δ ] (h G.⊗₁ i)
  ⊗-resp-∼ᴿ[] {ε = ε} {δ} {A} {B} {C} {D} {f} {h} {g} {i} =
    ⊗₁ᴳ-≈ᴿ[] {proj₁ A} {proj₂ A} {proj₁ B} {proj₂ B} {proj₁ C} {proj₂ C} {proj₁ D} {proj₂ D}
             {ε = ε} {δ = δ} {f = f} {h = h} {g = g} {i = i}

  ≈⇒∼ᴿ[0] : {A B : G.Obj} {f g : A G.⇒ B} → f G.≈ g → f ∼ᴿ[ 0ℚ ] g
  ≈⇒∼ᴿ[0] {A} {B} e = Equivalence.to ≈ᴿ⇔≈ᴿ[0] (≈ᴹ⇒≈ᴿ {proj₁ A ⊎ proj₂ B} {proj₂ A ⊎ proj₁ B} e)

  ∼ᴿ⇔∼ᴿ[0] : {A B : G.Obj} {f g : A G.⇒ B} → (f Q.∼ g) ⇔ (f ∼ᴿ[ 0ℚ ] g)
  ∼ᴿ⇔∼ᴿ[0] = ≈ᴿ⇔≈ᴿ[0]

  obs-∼ᴿ[] : {u v : 𝟘ᵒ G.⇒ Ωᵒ} → u ∼ᴿ[ ε ] v → Obs u Verdict.≈̄[ ε ] Obs v
  obs-∼ᴿ[] {u = u} {v} e = Verdict.slack λ δ pos →
    ≈ₚ[]-resp (≈sym (runᴹ≈runˢ u (ask tt out))) (≈sym (runᴹ≈runˢ v (ask tt out)))
              (Verdict.≈̄⇒≈ (e (closeˢ (ask tt out))) δ pos)

-- A closing context — an ancilla `Y`, a test `t`, a closure `m` — observes no
-- more than Δ.
close-∼ᴿ[] : {A B Y : G.Obj} (t : Y G.⊗₀ B G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ Y G.⊗₀ A) {f g : A G.⇒ B}
           → f ∼ᴿ[ ε ] g
           → Obs ((t G.∘ (G.id G.⊗₁ f)) G.∘ m) Verdict.≈̄[ ε ] Obs ((t G.∘ (G.id G.⊗₁ g)) G.∘ m)
close-∼ᴿ[] {ε = ε} t m e =
  obs-∼ᴿ[] (≈ᴿ[]-mono (≤-reflexive (trans (+-identityʳ _) (trans (+-identityˡ _) (+-identityˡ ε))))
             (∘-resp-∼ᴿ[] (∘-resp-∼ᴿ[] (refl′ t) (⊗-resp-∼ᴿ[] (refl′ G.id) e)) (refl′ m)))
  where
  refl′ : {A B : G.Obj} (h : A G.⇒ B) → h ∼ᴿ[ 0ℚ ] h
  refl′ h = Approximation.≈[]-refl approxᵒ {h}
