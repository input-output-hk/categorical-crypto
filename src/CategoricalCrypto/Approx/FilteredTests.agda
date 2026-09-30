{-# OPTIONS --safe --without-K #-}

-- `Approx.Filtered` at a non-discrete allowance poset: cost profiles `ℕ → ℕ`,
-- ordered and identified POINTWISE (stdlib's `IndexedPoset.poset`).  Profiles
-- agreeing at every argument need not be `≡` without funext, so doubling the
-- parameter as `n + n` and as `2 * n` gives two allowance maps whose outputs
-- no `≡`-comparison identifies; `Filt` identifies them, before and after
-- composition.

open import Categories.Category using (Category)

open import Data.Nat.Base using (ℕ; _+_; _*_; _≤_)
open import Data.Product.Base using (_,_; proj₂)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Indexed.Homogeneous.Bundles using (IndexedPoset)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)

import Data.Nat.Properties as ℕₚ

open import CategoricalCrypto.Approx.Error using (ℕ-ordered)

module CategoricalCrypto.Approx.FilteredTests where

Profiles : Poset 0ℓ 0ℓ 0ℓ
Profiles = IndexedPoset.poset {I = ℕ} record
  { Carrierᵢ        = λ _ → ℕ
  ; _≈ᵢ_            = _≡_
  ; _≤ᵢ_            = _≤_
  ; isPartialOrderᵢ = record
      { isPreorderᵢ = record
          { isEquivalenceᵢ = record { reflᵢ = refl ; symᵢ = sym ; transᵢ = trans }
          ; reflexiveᵢ     = ℕₚ.≤-reflexive
          ; transᵢ         = ℕₚ.≤-trans
          }
      ; antisymᵢ    = ℕₚ.≤-antisym
      }
  }

open import CategoricalCrypto.Approx.Controlled ℕ-ordered
open import CategoricalCrypto.Approx.Filtered ℕ-ordered Profiles

-- Runs are cost profiles too, compared exactly; a run is admitted at every
-- allowance it stays under.
Runs : FilteredSpace 0ℓ 0ℓ 0ℓ
Runs = record
  { space = record
      { Carrier = ℕ → ℕ
      ; approx  = record
          { _≈[_]_    = λ x _ y → (n : ℕ) → x n ≡ y n
          ; ≈[]-refl  = λ _ → refl
          ; ≈[]-sym   = λ h n → sym (h n)
          ; ≈[]-trans = λ h k n → trans (h n) (k n)
          ; ≈[]-mono  = λ _ h → h
          }
      }
  ; Admit      = λ a x → (n : ℕ) → x n ≤ a n
  ; admit-mono = λ le h n → ℕₚ.≤-trans (h n) (le n)
  }

-- Reading runs and allowances at `ρ n` instead of `n`.
along : (ℕ → ℕ) → Filtered Runs Runs
along ρ = record
  { underlying = record { map = _∘ ρ ; control = idᶜ ; preserves = λ h → h ∘ ρ }
  ; allowance  = record
      { ⟦_⟧                 = _∘ ρ
      ; isOrderHomomorphism = record { cong = _∘ ρ ; mono = _∘ ρ }
      }
  ; admits     = _∘ ρ
  }

module F = Category (Filt 0ℓ 0ℓ 0ℓ)

along-resp : {ρ σ : ℕ → ℕ} → ((n : ℕ) → ρ n ≡ σ n) → along ρ F.≈ along σ
along-resp eq = (≐-reflexive refl , λ x n → cong x (eq n)) , λ a n → cong a (eq n)

doubled : along (λ n → n + n) F.≈ along (2 *_)
doubled = along-resp λ n → cong (n +_) (sym (ℕₚ.+-identityʳ n))

doubled² : along (λ n → n + n) F.∘ along (λ n → n + n) F.≈ along (2 *_) F.∘ along (2 *_)
doubled² = F.∘-resp-≈ {f = along λ n → n + n} {h = along (2 *_)}
                      {g = along λ n → n + n} {i = along (2 *_)} doubled doubled

-- A run admitted at `a` is carried by one spelling to an output admitted at the
-- other spelling's allowance: admission moves along `_≈_`, not along `≡`.
admitted-doubled : {a x : ℕ → ℕ} → FilteredSpace.Admit Runs a x
                 → FilteredSpace.Admit Runs (a ∘ (2 *_)) (x ∘ λ n → n + n)
admitted-doubled {a} h =
  FilteredSpace.admit-resp Runs (proj₂ doubled a) (Filtered.admits (along λ n → n + n) h)
