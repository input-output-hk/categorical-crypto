{-# OPTIONS --safe --without-K #-}

-- A native family consumer: natural-number offsets compose and tensor by
-- addition, and a closed offset k reads as 2^-k in the faithful rational
-- metric.  Arbitrary test/closure offsets attenuate these readings, so the
-- negligible witness below can retain their actual, context-dependent values.
-- The simulator adds one; it is not the identity offset zero.

module CategoricalCrypto.UC.Family.Negligible.Tests where

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Properties as ℕₚ using (+-0-monoid; +-commutativeSemigroup)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties as ℚₚ using ()
open import Data.Unit.Polymorphic using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong₂; sym; trans)
open import Relation.Nullary using (¬_)

open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using (interchange)
open import Categories.Category.Construction.MonoidAsCategory 0ℓ +-0-monoid
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal using (monoidalHelper)
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2; 0≤inv-pow-2)
open import ProbabilisticLogic.Distribution.Uniform.Decay using (_→0)

open import CategoricalCrypto.Approx.Error using (Approximation; ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-+)
open import CategoricalCrypto.UC.Approximate.Decay using (negligible-slack)
open import CategoricalCrypto.UC.Approximate.Separating
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)
open import CategoricalCrypto.UCSetup.Morphism using (UCSetupMorphism)

import CategoricalCrypto.UC.Family as Familyᴹ
import CategoricalCrypto.UC.Family.Negligible as Negᴹ
import CategoricalCrypto.UC.Family.Negligible.Setup as Setupᴹ
import CategoricalCrypto.UC.Family.Negligible.Vanishing as Refineᴹ

Offsets : MonoidalCategory 0ℓ 0ℓ 0ℓ
Offsets = record
  { U = MonoidAsCategory
  ; monoidal = monoidalHelper MonoidAsCategory record
    { ⊗ = record
      { F₀ = λ _ → tt ; F₁ = λ (f , g) → f ℕ.+ g
      ; identity = refl
      ; homomorphism = λ where
          {f = f₁ , f₂} {g = g₁ , g₂} → interchange g₁ f₁ g₂ f₂
      ; F-resp-≈ = λ (p , q) → cong₂ ℕ._+_ p q }
    ; unit = tt
    ; unitorˡ = record { from = 0 ; to = 0 ; iso = record { isoˡ = refl ; isoʳ = refl } }
    ; unitorʳ = record { from = 0 ; to = 0 ; iso = record { isoˡ = refl ; isoʳ = refl } }
    ; associator = record { from = 0 ; to = 0 ; iso = record { isoˡ = refl ; isoʳ = refl } }
    ; unitorˡ-commute = sym (ℕₚ.+-identityʳ _)
    ; unitorʳ-commute = trans (ℕₚ.+-identityʳ _) (sym (ℕₚ.+-identityʳ _))
    ; assoc-commute = λ where
        {f = f} {g = g} {h = h} →
          trans (ℕₚ.+-assoc f g h) (sym (ℕₚ.+-identityʳ (f ℕ.+ (g ℕ.+ h))))
    ; triangle = refl ; pentagon = refl }
  }

qread : QEvaluation (MonoidalCategory.U Offsets) 0ℓ 0ℓ
qread = record
  { J = tt ; Ω = tt ; X = record { Carrier = ℚ ; approx = ℚ-metric }
  ; eval₀ = record
    { to = inv-pow-2
    ; cong = λ { {x} refl → Approximation.≈[]-refl ℚ-metric {x = inv-pow-2 x} } } }

private module Rates = SymmetricMonoidalCategory Rates

grading : GradedSubCat Rates.monoidalCategory Offsets 0ℓ
grading = unrestricted Rates.monoidalCategory Offsets

module F = Familyᴹ Offsets qread grading ℕ (λ n → n) (λ n → n , ℕₚ.≤-refl)
  using (Obj^ω; _⇒^ω_; _⊛ω_; Δ; unit^ω; hom; Evaluation^ω)
module N = Negᴹ Offsets qread grading ℕ (λ n → n) (λ n → n , ℕₚ.≤-refl)
  using (Evaluationᴺ)
module C = Setupᴹ.Canonicalᴺ Offsets qread grading ℕ (λ n → n) (λ n → n , ℕₚ.≤-refl)
  using (_∘_; sub; _≈ᵁ_; _≤UC_; dummy-complete; module KE)
module V = Refineᴹ Offsets qread grading ℕ (λ n → n) (λ n → n , ℕₚ.≤-refl)
  using (negligible⇒vanishing; ≈ᵁᴺ⇒≈ᵁω; ≤UCᴺ⇒≤UCω; same-simulator; module Target)
module W = V.Target
module Morph = UCSetupMorphism V.negligible⇒vanishing
  using (κ; module F; module Φ; module ν)

private
  module G = GradedSubCat grading using (⌊_⌋)
  module ON = Observable (Evaluation.observable N.Evaluationᴺ) using (Test; _≋_)
  module OW = Observable (Evaluation.observable F.Evaluation^ω) using (_≋_)

level : {A B : F.Obj^ω} → A F.⇒^ω B → ℕ → ℕ
level f n = G.⌊ F.hom f n ⌋

arrow : {A B : F.Obj^ω} → (ℕ → ℕ) → A F.⇒^ω B
arrow f = F.unit^ω λ n → f n , tt

𝟙 : F.Obj^ω
𝟙 = F.Δ tt

real ideal simulator : 𝟙 F.⇒^ω (𝟙 F.⊛ω 𝟙)
real = arrow (λ n → n ℕ.+ 2)
ideal = arrow (λ n → n)
simulator = arrow (λ _ → 1)

-- These are the actual closed exponents, including both native contexts.
closed-level : {A B : F.Obj^ω} (f : A F.⇒^ω B) (t : ON.Test B)
               (m : Evaluation.Closure N.Evaluationᴺ A) → ℕ → ℕ
closed-level f t m = level ((t C.∘ f) C.∘ m)

local-error : {A B : F.Obj^ω} (f g : A F.⇒^ω B) (t : ON.Test B)
              (m : Evaluation.Closure N.Evaluationᴺ A) → ℕ → ℚ
local-error f g t m n = inv-pow-2 (closed-level f t m n) ℚ.+ inv-pow-2 (closed-level g t m n)

closed-lower : {A B : F.Obj^ω} (f : A F.⇒^ω B) → ((n : ℕ) → n ℕ.≤ level f n)
               → (t : ON.Test B) (m : Evaluation.Closure N.Evaluationᴺ A)
               → (n : ℕ) → n ℕ.≤ closed-level f t m n
closed-lower f lo t m n = ℕₚ.≤-trans
  (ℕₚ.≤-trans (lo n) (ℕₚ.m≤n+m (level f n) (level t n)))
  (ℕₚ.m≤m+n (level t n ℕ.+ level f n) (level m n))

native-local : {A B : F.Obj^ω} (f g : A F.⇒^ω B)
               → ((n : ℕ) → n ℕ.≤ level f n) → ((n : ℕ) → n ℕ.≤ level g n)
               → (t : ON.Test B) → (t C.∘ f) ON.≋ (t C.∘ g)
native-local f g lf lg t m = local-error f g t m
  , Negligible-+ (negligible-slack (closed-lower f lf t m))
                 (negligible-slack (closed-lower g lg t m))
  , λ n →
      let a = closed-level f t m n ; b = closed-level g t m n
      in ℚₚ.≤-trans (ℚₚ.∣p-q∣≤∣p∣+∣q∣ (inv-pow-2 a) (inv-pow-2 b))
           (ℚₚ.≤-reflexive (cong₂ ℚ._+_ (ℚₚ.0≤p⇒∣p∣≡p (0≤inv-pow-2 a))
                                          (ℚₚ.0≤p⇒∣p∣≡p (0≤inv-pow-2 b))))

native-U : (f g : 𝟙 F.⇒^ω (𝟙 F.⊛ω 𝟙))
           → ((n : ℕ) → n ℕ.≤ level f n) → ((n : ℕ) → n ℕ.≤ level g n)
           → f C.≈ᵁ g
native-U f g lf lg Y = C.KE.mk∼ λ {t} → native-local f g lf lg t

real≈simulatedᴺ : real C.≈ᵁ (C.sub simulator C.∘ ideal)
real≈simulatedᴺ = native-U real (C.sub simulator C.∘ ideal)
  (λ n → ℕₚ.m≤m+n n 2) (λ n → ℕₚ.m≤n+m n 1)

real≤idealᴺ : real C.≤UC ideal
real≤idealᴺ = C.dummy-complete {f = real} {g = ideal} (simulator , real≈simulatedᴺ)

real≈simulatedω : real W.≈ᵁ (C.sub simulator C.∘ ideal)
real≈simulatedω = V.≈ᵁᴺ⇒≈ᵁω real (C.sub simulator C.∘ ideal) real≈simulatedᴺ

real≤idealω : real W.≤UC ideal
real≤idealω = V.≤UCᴺ⇒≤UCω real ideal real≤idealᴺ

same-native-simulator : (a : 𝟙 F.⇒^ω 𝟙)
                        → proj₁ (real≤idealω a) ≡ proj₁ (real≤idealᴺ a)
same-native-simulator = V.same-simulator real ideal real≤idealᴺ

dummy : 𝟙 F.⇒^ω 𝟙
dummy = arrow (λ _ → 0)

simulator-adds-one : (n : ℕ) → level (proj₁ (real≤idealω dummy)) n ≡ 1
simulator-adds-one n = refl

simulator-not-identity : level simulator 0 ≢ level dummy 0
simulator-not-identity ()

native-observationᴺ : (t : ON.Test (𝟙 F.⊛ω 𝟙)) → (t C.∘ real) ON.≋ (t C.∘ ideal)
native-observationᴺ = native-local real ideal (λ n → ℕₚ.m≤m+n n 2) (λ n → ℕₚ.≤-refl)

native-observationω : (t : ON.Test (𝟙 F.⊛ω 𝟙)) → (t C.∘ real) OW.≋ (t C.∘ ideal)
native-observationω t = Func.cong (Morph.ν.η (𝟙 F.⊛ω 𝟙))
  {x = t C.∘ real} {y = t C.∘ ideal} (native-observationᴺ t)

context-zero context-one : ON.Test (𝟙 F.⊛ω 𝟙)
context-zero = arrow (λ _ → 0)
context-one = arrow (λ _ → 1)

context-witnesses-differ : proj₁ (native-observationᴺ context-zero dummy) 0
                         ≢ proj₁ (native-observationᴺ context-one dummy) 0
context-witnesses-differ ()

closure-one : Evaluation.Closure N.Evaluationᴺ 𝟙
closure-one = arrow (λ _ → 1)

closure-witnesses-differ : proj₁ (native-observationᴺ context-zero dummy) 0
                         ≢ proj₁ (native-observationᴺ context-zero closure-one) 0
closure-witnesses-differ ()

closed-native-readings-differ :
    Evaluation.observe N.Evaluationᴺ (context-zero C.∘ real) dummy 0
  ≢ Evaluation.observe N.Evaluationᴺ (context-zero C.∘ (C.sub simulator C.∘ ideal)) dummy 0
closed-native-readings-differ ()

consumer-map-identity : (t : ON.Test (𝟙 F.⊛ω 𝟙))
                        → Morph.ν.η (𝟙 F.⊛ω 𝟙) ⟨$⟩ t ≡ t
consumer-map-identity t = refl

carrier-action-identity : {A B : F.Obj^ω} (f : A F.⇒^ω B) → Morph.F.₁ f ≡ f
carrier-action-identity f = refl

grade-action-identity : {A B : F.Obj^ω} (s : A F.⇒^ω B) → Morph.Φ.₁ s ≡ s
grade-action-identity s = refl

comparison-identity : Morph.κ {X = 𝟙} {A = 𝟙} ≡ dummy
comparison-identity = refl

-- Scalar separation only: this is not a UC nonreflection counterexample.
scalar-vanishes : inv-suc →0
scalar-vanishes = inv-suc-→0

scalar-not-negligible : ¬ Negligible inv-suc
scalar-not-negligible = ¬negligible-inv-suc
