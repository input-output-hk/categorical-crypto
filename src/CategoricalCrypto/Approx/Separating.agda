{-# OPTIONS --safe --without-K #-}

-- The example keeping `F₀` and `F₊` apart
-- (`docs/quantitative-uc-setup-plan.typ` §3).
--
-- The two forgetful functors differ exactly where a space's error balls are not
-- closed, and one space is enough to show that they do: rational sequences
-- compared by EVENTUAL closeness.  `2⁻ⁿ` is eventually within every positive ε
-- of the zero sequence and is never eventually equal to it.
--
-- The plan's own witness is the model-level one; this is the same phenomenon on
-- the smallest carrier that exhibits it.

open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties.Ext
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Approximate.Separating

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.Approx.Separating where

open import CategoricalCrypto.Approx.Forget ℚ-ordered ℚ-refinement 0ℓ 0ℓ
open import CategoricalCrypto.Approx.Space ℚ-ordered

zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

infix 4 _≈ᵉ[_]_

_≈ᵉ[_]_ : (ℕ → ℚ) → ℚ → (ℕ → ℚ) → Set
s ≈ᵉ[ ε ] t = Σ[ N ∈ ℕ ] ((n : ℕ) → N ℕ.≤ n → ∣ s n ℚ.- t n ∣ ℚ.≤ ε)

-- A negative ε admits nothing, so the laws never have to weigh one: an absolute
-- value under it is already absurd.
eventually : Approximation (ℕ → ℚ) ℚ-ordered 0ℓ
eventually = record
  { _≈[_]_    = _≈ᵉ[_]_
  ; ≈[]-refl  = λ {s} → 0 , λ n _ → ℚₚ.≤-reflexive (∣x-x∣≡0 (s n))
  ; ≈[]-sym   = λ {s} {t} (N , b) → N ,
      λ n le → subst (ℚ._≤ _) (∣-∣-comm (s n) (t n)) (b n le)
  ; ≈[]-trans = λ {s} {t} {u} (N₁ , b₁) (N₂ , b₂) → N₁ ℕ.⊔ N₂ ,
      λ n le → ℚₚ.≤-trans (∣-∣-triangle (s n) (t n) (u n))
                 (ℚₚ.+-mono-≤ (b₁ n (ℕₚ.≤-trans (ℕₚ.m≤m⊔n N₁ N₂) le))
                              (b₂ n (ℕₚ.≤-trans (ℕₚ.m≤n⊔m N₁ N₂) le)))
  ; ≈[]-mono  = λ le (N , b) → N , λ n l → ℚₚ.≤-trans (b n l) le
  }

Sequences : ApproxSpace 0ℓ 0ℓ
Sequences = record { Carrier = ℕ → ℚ ; approx = eventually }

------------------------------------------------------------------------
-- …and the two forgetful functors disagree on one pair

F₊-identifies : Setoid._≈_ ⟦ Sequences ⟧₊ inv-pow-2 zeroᶠ
F₊-identifies ε pos =
  let N , bnd = Negligible⇒→0 (negligible-slack (λ _ → ℕₚ.≤-refl)) ε pos
  in N , λ n le → ℚₚ.≤-trans (≈ᵐ-0 (ℚₚ.<⇒≤ (0<inv-pow-2 n))) (bnd n le)

F₀-separates : ¬ Setoid._≈_ ⟦ Sequences ⟧₀ inv-pow-2 zeroᶠ
F₀-separates (N , bnd) = ℚₚ.<-irrefl refl
  (ℚₚ.<-≤-trans (0<inv-pow-2 N) (≈ᵐ-gap (bnd N ℕₚ.≤-refl)))
