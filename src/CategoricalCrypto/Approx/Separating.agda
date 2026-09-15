{-# OPTIONS --safe --without-K #-}

-- The example keeping `F₀` and `F₊` apart
-- (`docs/quantitative-uc-setup-plan.typ` §3).
--
-- The two forgetful functors differ exactly where a space's error balls are not
-- closed, and one space is enough to show that they do: rational sequences
-- compared by EVENTUAL closeness.  `2⁻ⁿ` is eventually within every positive ε
-- of the zero sequence and is never eventually equal to it, so `F₊` identifies
-- the pair and `F₀` separates it.  Hence an exact bound must be stated in
-- `Approx`, never asked to respect `F₊`'s equality.
--
-- The plan's own witness is the model-level one — a finite-stage observation
-- telling an immediate return from an almost-sure geometric one.  This is the
-- same phenomenon on the smallest carrier that exhibits it, and it reuses the
-- decay facts (`UC.Approximate.Decay`) that witness already spends.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ∣_∣)
open import Data.Rational.Properties.Ext using (∣-∣-comm; ∣-∣-triangle; ∣x-x∣≡0)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Relation.Nullary using (¬_)

open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.UC.Approximate using (Approximation; Negligible⇒→0; ℚ-errors)
open import CategoricalCrypto.UC.Approximate.Decay using (0<inv-pow-2; negligible-slack)
open import CategoricalCrypto.UC.Approximate.Separating using (≈ᵐ-0; ≈ᵐ-gap)

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.Approx.Separating where

open import CategoricalCrypto.Approx.Forget ℚ-ordered 0ℓ 0ℓ
open import CategoricalCrypto.Approx.Space ℚ-ordered

zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

infix 4 _≈ᵉ[_]_

_≈ᵉ[_]_ : (ℕ → ℚ) → ℚ → (ℕ → ℚ) → Set
s ≈ᵉ[ ε ] t = Σ[ N ∈ ℕ ] ((n : ℕ) → N ℕ.≤ n → ∣ s n ℚ.- t n ∣ ℚ.≤ ε)

-- A negative ε admits nothing, so the laws never have to weigh one: an absolute
-- value under it is already absurd.
eventually : Approximation (ℕ → ℚ) ℚ-errors 0ℓ
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
