{-# OPTIONS --safe --without-K #-}

-- Computed pins for pick-ahead compilation.  The two-site composite
-- `veto ∘⁺ pick`, closed by a test that queues picks and then queries,
-- evaluates by `refl`: site 0 is the lower protocol's, a site's picks pop
-- oldest first, and a query whose site has nothing queued is `dead` — both
-- verdict masses vanish.  The concrete forms of `Choice.Compose` are the
-- setup's `_∙_` and `sub` at the curried tensor, also by `refl`.

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational using (0ℚ; 1ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Prᵇ⊥)

open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Setup using (_∙_; sub; module 𝒞)

module CategoricalCrypto.ND.SSP.Choice.Pin where

-- Answer with the pick.
pick : Protocol⁺ (Bool ∷ []) unitᴵ Ωᴵ
pick = record { St = ⊤ ; init = tt ; step = λ _ _ _ → choose (inj₁ tt) λ b → ret (tt , b) }

-- Ask below, pick a veto, pass the answer on unless vetoed.
veto : Protocol⁺ (Bool ∷ []) Ωᴵ Ωᴵ
veto = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → call tt tt λ b → choose (inj₁ tt) λ v → ret (tt , b ∧ not v) }

both : Protocol⁺ (Bool ∷ Bool ∷ []) unitᴵ Ωᴵ
both = veto ∘⁺ pick

-- Queue `true, false` on site 0 and `false, false` on site 1, query twice, and
-- report whether the answers were `true` then `false`.
script : Protocol (Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧ ⊗ᴵ Ωᴵ) Ωᴵ
script = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ →
      call (inj₁ (inj₁ tt)) true λ _ → call (inj₁ (inj₁ tt)) false λ _ →
      call (inj₁ (inj₂ (inj₁ tt))) false λ _ → call (inj₁ (inj₂ (inj₁ tt))) false λ _ →
      call (inj₂ tt) tt λ b → call (inj₂ tt) tt λ b′ → ret (tt , b ∧ not b′) }

-- Only site 1 is fed: `pick`'s choice finds its queue empty.
starve : Protocol (Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧ ⊗ᴵ Ωᴵ) Ωᴵ
starve = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → call (inj₁ (inj₂ (inj₁ tt))) false λ _ → call (inj₂ tt) tt λ b → ret (tt , b) }

script-both : Prᵇ⊥ true (runᵖ (script ∘ᵖ ⌈ both ⌉)) ≡ 1ℚ
script-both = refl

starve-both : Prᵇ⊥ true (runᵖ (starve ∘ᵖ ⌈ both ⌉)) ≡ 0ℚ
starve-both = refl

starve-both-false : Prᵇ⊥ false (runᵖ (starve ∘ᵖ ⌈ both ⌉)) ≡ 0ℚ
starve-both-false = refl

module _ {S⃗ T⃗ : List Set} {A B C : Iface} (g : Protocol⁺ T⃗ B C) (f : Protocol⁺ S⃗ A B) where

  ∙-concrete : ⌈ g ⌉ ∙ ⌈ f ⌉ ≡ ⌜ αᴵ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ⌈ g ⌉ ∘ᵖ ⌈ f ⌉
  ∙-concrete = refl

  sub-concrete : sub ⌜ join S⃗ T⃗ ⌝ 𝒞.∘ ⌈ g ∘⁺ f ⌉ ≡ ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌈ g ∘⁺ f ⌉
  sub-concrete = refl
