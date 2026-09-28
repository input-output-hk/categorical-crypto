{-# OPTIONS --safe --without-K #-}

-- `audit-carry`: an ideal-side bound on the mass a permitted context observes carries to
-- the real side at the emulation's slack, with the simulator absorbed into the test and the
-- budget scaled by its rate. A `Context` is an ancilla, a test and a closure; a `Certified`
-- one carries rate-certified witnesses of its test and closure, whose rates give its
-- budget; a `Permitted` class is the certified contexts trusted to read the event. Masses
-- are lower reals presented by rational sequences (`Data.Rational.LowerReal`, after
-- Coquand–Spitters).

import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Monoidal
open import Categories.LocallyGraded.SubCategory
import Categories.Morphism.Reasoning as MR

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.LowerReal hiding (_≈_)
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality hiding (J)
open import Relation.Unary using (_⊆_)

import CategoricalCrypto.Standard2 as Std2
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Audit
  {o ℓ e cs ℓs qs : Level} (M : MonoidalCategory o ℓ e)
  (R : Evaluation (MonoidalCategory.U M) cs ℓs)
  (Rg : GradedSubCat Rates.monoidalCategory M qs) (mass : Func (Evaluation.S R) LowerReal) where

open Evaluation R
open Observable observable using (Test; ℰᴼ)
open Std2.StdUC M ℰᴼ

open GradedSubCat Rg
module L = LocallyGradedCategory L
open GradedMonoidal (monoidalᴸ Rates.braided) using () renaming (_⊗₁_ to _⊗ʰ_)

private variable A B′ X Z : Channel
                 w w′ : Level
                 r : ℕ⁺

infix 4 _≤UC[_]_
infixl 7 _∙ᶜ_ _∙ˢ_

_≤UC[_]_ : {A B′ X Y : Channel} → A ⇒ X ⊗₀ B′ → ℕ⁺ → A ⇒ Y ⊗₀ B′ → Set (o ⊔ ℓ ⊔ ℓs ⊔ qs)
_≤UC[_]_ {X = X} {Y} f r g = Σ[ ŝ ∈ L.Hom r Y X ] f ≈ᵁ (⌊ ŝ ⌋ ⊗₁ id ∘ g)

≤UC[]⇒≤UC : {f : A ⇒ X ⊗₀ B′} {g : A ⇒ Z ⊗₀ B′} → f ≤UC[ r ] g → f ≤UC g
≤UC[]⇒≤UC (ŝ , h) = dummy-complete (⌊ ŝ ⌋ , h)

record Context (A X B′ : Channel) : Set (o ⊔ ℓ) where
  field Y  : Channel
        Et : Test (Y ⊗₀ (X ⊗₀ B′))
        m  : Closure (Y ⊗₀ A)

observeᶜ : Context A X B′ → A ⇒ X ⊗₀ B′ → S.Carrier
observeᶜ k f = observe (Et ∘ id ⊗₁ f) m where open Context k

_∙ᶜ_ : Context A X B′ → Z ⇒ X → Context A Z B′
k ∙ᶜ s = record { Y = Y ; Et = Et ∘ id ⊗₁ (s ⊗₁ id) ; m = m } where open Context k

record Certified (A X B′ : Channel) : Set (o ⊔ ℓ ⊔ e ⊔ qs) where
  field ctx  : Context A X B′
        c r′ : ℕ⁺
  open Context ctx
  field Êt  : L.Hom c (Y ⊗₀ (X ⊗₀ B′)) Ω
        m̂   : L.Hom r′ J (Y ⊗₀ A)
        Êt≈ : ⌊ Êt ⌋ ≈ Et
        m̂≈  : ⌊ m̂ ⌋ ≈ m

  budget : ℕ
  budget = value (c · r′)

open Certified

_∙ˢ_ : Certified A X B′ → L.Hom r Z X → Certified A Z B′
_∙ˢ_ {r = r} k ŝ = record
  { ctx = ctx k ∙ᶜ ⌊ ŝ ⌋ ; c = c k · r ; r′ = r′ k ; m̂ = m̂ k ; m̂≈ = m̂≈ k
  ; Êt  = L.sub[ ≤-reflexive (trans (cong (ℕ._* value (c k)) (trans (*-identityˡ _) (*-identityʳ (value r))))
                                     (*-comm (value r) (value (c k)))) ]
            (Êt k L.∙ (L.id ⊗ʰ (ŝ ⊗ʰ L.id)))
  ; Êt≈ = ∘-resp-≈ˡ (Êt≈ k) }

budget-∙ˢ : (k : Certified A X B′) (ŝ : L.Hom r Z X) → budget (k ∙ˢ ŝ) ≡ scale (budget k) r
budget-∙ˢ {r = r} k _ = xy∙z≈xz∙y (value (c k)) (value r) (value (r′ k))
  where open CommSemigroupProperties *-commutativeSemigroup

Permitted : (w : Level) (A X B′ : Channel) → Set (o ⊔ ℓ ⊔ e ⊔ qs ⊔ suc w)
Permitted w A X B′ = Certified A X B′ → Set w

AuditBound : A ⇒ X ⊗₀ B′ → Permitted w A X B′ → (ℕ → ℚ) → Set (o ⊔ ℓ ⊔ e ⊔ qs ⊔ w)
AuditBound f 𝔈 ε = ∀ k → 𝔈 k → mass ⟨$⟩ observeᶜ (ctx k) f ≤ℚ ε (budget k)

pinned : A ⇒ X ⊗₀ B′ → (ℕ → S.Carrier) → Permitted ℓs A X B′
pinned f μ k = observeᶜ (ctx k) f S.≈ μ (budget k)

-- The slack is the price of reading an equality of lower reals as a numeric comparison.
pinned-bound : (f : A ⇒ X ⊗₀ B′) (μ : ℕ → S.Carrier) (ε : ℕ → ℚ) (δ : ℚ) → 0ℚ ℚ.< δ
             → ((q : ℕ) → mass ⟨$⟩ μ q ≤ℚ ε q) → AuditBound f (pinned f μ) (λ q → ε q ℚ.+ δ)
pinned-bound f μ ε δ δ>0 bnd k ev = ≲-≤ℚ _ _ (≈⇒≲ _ _ (Func.cong mass ev)) (bnd (budget k)) δ δ>0

absorb : L.Hom r Z X → Permitted w A Z B′ → Permitted w A X B′
absorb ŝ 𝔉 k = 𝔉 (k ∙ˢ ŝ)

Absorbs : L.Hom r Z X → Permitted w A X B′ → Permitted w′ A Z B′ → Set _
Absorbs ŝ 𝔈 𝔉 = 𝔈 ⊆ absorb ŝ 𝔉

≈ᵁ-at : {f : A ⇒ X ⊗₀ B′} {g : A ⇒ Z ⊗₀ B′} (s : Z ⇒ X) → f ≈ᵁ (s ⊗₁ id ∘ g)
      → (k : Context A X B′) → observeᶜ k f S.≈ observeᶜ (k ∙ᶜ s) g
≈ᵁ-at {f = f} {g} s em k = read-cast (cast f) (cast (s ⊗₁ id ∘ g) ○ ∘-resp-≈ˡ (pushʳ T-homomorphism))
                                     (KE.run∼ (em Y) {Et ∘ α⇒} m)
  where
  open Context k
  open HomReasoning
  open MR ∣machines∣
  cast = λ w → pullʳ (cancelˡ associator.isoʳ) ⟩∘⟨refl

audit-carry : (f : A ⇒ X ⊗₀ B′) (g : A ⇒ Z ⊗₀ B′) (em : f ≤UC[ r ] g)
              {𝔈 : Permitted w A X B′} {𝔉 : Permitted w′ A Z B′} → Absorbs (proj₁ em) 𝔈 𝔉
            → (ε : ℕ → ℚ) (δ : ℚ) → 0ℚ ℚ.< δ
            → AuditBound g 𝔉 ε → AuditBound f 𝔈 (λ q → ε (scale q r) ℚ.+ δ)
audit-carry f g (ŝ , em) cl ε δ δ>0 bnd k ev =
  subst (λ q → mass ⟨$⟩ observeᶜ (ctx k) f ≤ℚ ε q ℚ.+ δ) (budget-∙ˢ k ŝ)
        (≲-≤ℚ _ _ (≈⇒≲ _ _ (Func.cong mass (≈ᵁ-at ⌊ ŝ ⌋ em (ctx k)))) (bnd (k ∙ˢ ŝ) (cl ev)) δ δ>0)
