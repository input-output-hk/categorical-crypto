{-# OPTIONS --safe --without-K --guardedness #-}

-- Distinguishing advantage on `Dₚ Bool` as a relation indexed by a rational
-- slack: the mass is a supremum never formed (see `Dp`), so there is no
-- `adv : … → ℚ`.
--
-- Both verdict masses are compared: observing only the `true`-mass identifies an
-- implementation that answers `false` with one that diverges, since divergence
-- weighs 0 under either indicator.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties

open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Advantage where

private variable d e h d′ e′ : Dₚ Bool
                 ε δ r r′ : ℚ

Pr≤[_] : Bool → ℕ → Dₚ Bool → ℚ
Pr≤[ b ] n d = cum n d (indᵇ b)

Pr≤ : ℕ → Dₚ Bool → ℚ
Pr≤ = Pr≤[ true ]

indᵇ-not : (b : Bool) → indᵇ b (not b) ≡ 0ℚ
indᵇ-not true  = refl
indᵇ-not false = refl

-- A verdict scores at most what a flag covering it scores.
indᵇ-cover : {v b : Bool} → (v ≡ true → b ≡ true) → indᵇ true v ℚ.≤ indᵇ true b
indᵇ-cover {false} {b} h = ≤-trans (≤-reflexive (indᵇ-not true)) (indᵇ-nn true b)
indᵇ-cover {true}      h = ≤-reflexive (cong (indᵇ true) (sym (h refl)))

Pr≤-mono : {n m : ℕ} (b : Bool) (d : Dₚ Bool) → n ≤ℕ m → Pr≤[ b ] n d ℚ.≤ Pr≤[ b ] m d
Pr≤-mono b d le = cum-mono le d (indᵇ b) (indᵇ-nn b)

infix 4 _≼ₚ[_]_ _≈ₚ[_]_

_≼ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≼ₚ[ ε ] e = (b : Bool) → Dom (indᵇ b) ε d e

_≈ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≈ₚ[ ε ] e = (d ≼ₚ[ ε ] e) × (e ≼ₚ[ ε ] d)

------------------------------------------------------------------------
-- The pseudometric laws

≼ₚ⇒≼ₚ[0] : d ≼ₚ e → d ≼ₚ[ 0ℚ ] e
≼ₚ⇒≼ₚ[0] le b = cofinal⇒dom (le (indᵇ b) (indᵇ-nn b))

≼ₚ[]-refl : d ≼ₚ[ 0ℚ ] d
≼ₚ[]-refl {d} = ≼ₚ⇒≼ₚ[0] (≼ₚ-refl d)

≼ₚ[]-mono : ε ℚ.≤ δ → d ≼ₚ[ ε ] e → d ≼ₚ[ δ ] e
≼ₚ[]-mono le h b = dom-mono le (h b)

≼ₚ[]-trans : d ≼ₚ[ ε ] e → e ≼ₚ[ δ ] h → d ≼ₚ[ ε ℚ.+ δ ] h
≼ₚ[]-trans p q b = dom-trans (p b) (q b)

≼ₚ[]-resp : d′ ≼ₚ d → e ≼ₚ e′ → d ≼ₚ[ ε ] e → d′ ≼ₚ[ ε ] e′
≼ₚ[]-resp l r p b = dom-resp (l (indᵇ b) (indᵇ-nn b)) (r (indᵇ b) (indᵇ-nn b)) (p b)

≈ₚ⇒≈ₚ[0] : d ≈ₚ e → d ≈ₚ[ 0ℚ ] e
≈ₚ⇒≈ₚ[0] (le , el) = ≼ₚ⇒≼ₚ[0] le , ≼ₚ⇒≼ₚ[0] el

≈ₚ[]-refl : d ≈ₚ[ 0ℚ ] d
≈ₚ[]-refl {d} = ≈ₚ⇒≈ₚ[0] (≈ₚ-refl d)

≈ₚ[]-sym : d ≈ₚ[ ε ] e → e ≈ₚ[ ε ] d
≈ₚ[]-sym (le , el) = el , le

≈ₚ[]-mono : ε ℚ.≤ δ → d ≈ₚ[ ε ] e → d ≈ₚ[ δ ] e
≈ₚ[]-mono le (p , q) = ≼ₚ[]-mono le p , ≼ₚ[]-mono le q

≈ₚ[]-trans : d ≈ₚ[ ε ] e → e ≈ₚ[ δ ] h → d ≈ₚ[ ε ℚ.+ δ ] h
≈ₚ[]-trans {ε = ε} {δ = δ} (p , p′) (q , q′) =
  ≼ₚ[]-trans p q , ≼ₚ[]-mono (≤-reflexive (+-comm δ ε)) (≼ₚ[]-trans q′ p′)

≈ₚ[]-resp : d ≈ₚ d′ → e ≈ₚ e′ → d ≈ₚ[ ε ] e → d′ ≈ₚ[ ε ] e′
≈ₚ[]-resp (dd , dd′) (ee , ee′) (p , q) = ≼ₚ[]-resp dd′ ee p , ≼ₚ[]-resp ee′ dd q

------------------------------------------------------------------------
-- One-sided upper bounds

-- A bound on the `true`-mass at every approximant.  Not `_≈ₚ[_]_` against
-- `returnₚ false`, which also constrains the `false`-mass and fails at `botₚ`.
Upper : Dₚ Bool → ℚ → Set
Upper d r = (k : ℕ) → Pr≤ k d ℚ.≤ r

upper-mono : r ℚ.≤ r′ → Upper d r → Upper d r′
upper-mono le up k = ≤-trans (up k) le

upper-dom : Dom (indᵇ true) ε d e → Upper e r → Upper d (r ℚ.+ ε)
upper-dom {ε = ε} le up k = let m , bd = le k in ≤-trans bd (+-monoˡ-≤ ε (up m))

upper-≼[] : d ≼ₚ[ ε ] e → Upper e r → Upper d (r ℚ.+ ε)
upper-≼[] le = upper-dom (le true)

upper-≈[] : d ≈ₚ[ ε ] e → Upper e r → Upper d (r ℚ.+ ε)
upper-≈[] (le , _) = upper-≼[] le

upper-≼ : d ≼ₚ e → Upper e r → Upper d r
upper-≼ le up k = let m , bd = le _ (indᵇ-nn true) k in ≤-trans bd (up m)

upper-≈ : d ≈ₚ e → Upper e r → Upper d r
upper-≈ (le , _) = upper-≼ le
