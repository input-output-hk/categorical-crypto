{-# OPTIONS --safe --without-K #-}

-- Approximations with rational errors: the slack closure
-- (`docs/quantitative-uc-setup-plan.typ` §3, "Optional closedness") and the
-- hybrid lemma.
--
-- `x ≈̄[ ε ] y` asks for `x ≈[ ε + δ ] y` at every positive δ.  It is closed
-- (`≈̄-closed`) and its zero error IS the all-positive collapse (`≈̄[0]⇔∼ᵃ`),
-- so a bound survives a `∼ᵃ`-change of either endpoint (`≈̄-resp-∼ᵃ`): what a
-- distance on the quotient by `∼ᵃ` needs.  The converse of `≈⇒≈̄` fails
-- wherever the original balls are not closed (`Approx.Separating`).

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Fin.Base using (Fin; zero; suc; inject₁; fromℕ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext using (p≤p+q; 0<½*; ½*+½*)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
import Algebra.Properties.CommutativeSemigroup as CommSemigroup
import Algebra.Properties.Monoid.Sum as Sum

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Rational where

open Sum +-0-monoid

private
  open CommSemigroup (CommutativeMonoid.commutativeSemigroup +-0-commutativeMonoid)
  variable o ℓa : Level

------------------------------------------------------------------------
-- The slack closure

module Closure {Obs : Set o} (A : Approximation Obs ℚ-ordered ℓa) where

  open Approximation A
  open AllPositive ℚ-refinement A using (_∼ᵃ_)

  infix 4 _≈̄[_]_

  -- A record rather than its field's Π-type: `ε` is then recoverable by
  -- unification, which `ε + δ` alone does not allow.
  record _≈̄[_]_ (x : Obs) (ε : ℚ) (y : Obs) : Set ℓa where
    constructor slack
    field ≈̄⇒≈ : (δ : ℚ) → 0ℚ ℚ.< δ → x ≈[ ε ℚ.+ δ ] y

  open _≈̄[_]_ public

  private variable
    x x′ y y′ z : Obs
    ε ε′ : ℚ

  ≈⇒≈̄ : x ≈[ ε ] y → x ≈̄[ ε ] y
  ≈⇒≈̄ {ε = ε} h = slack λ δ pos → ≈[]-mono (p≤p+q ε (<⇒≤ pos)) h

  ≈̄-trans : x ≈̄[ ε ] y → y ≈̄[ ε′ ] z → x ≈̄[ ε ℚ.+ ε′ ] z
  ≈̄-trans {ε = ε} {ε′ = ε′} h k = slack λ δ pos →
    ≈[]-mono (≤-reflexive (trans (interchange ε (½ ℚ.* δ) ε′ (½ ℚ.* δ))
                                 (cong ((ε ℚ.+ ε′) ℚ.+_) (½*+½* δ))))
             (≈[]-trans (≈̄⇒≈ h (½ ℚ.* δ) (0<½* pos)) (≈̄⇒≈ k (½ ℚ.* δ) (0<½* pos)))

  closure : Approximation Obs ℚ-ordered ℓa
  closure = record
    { _≈[_]_    = _≈̄[_]_
    ; ≈[]-refl  = ≈⇒≈̄ ≈[]-refl
    ; ≈[]-sym   = λ h → slack λ δ pos → ≈[]-sym (≈̄⇒≈ h δ pos)
    ; ≈[]-trans = ≈̄-trans
    ; ≈[]-mono  = λ le h → slack λ δ pos → ≈[]-mono (+-monoˡ-≤ δ le) (≈̄⇒≈ h δ pos)
    }

  ≈̄-closed : ((δ : ℚ) → 0ℚ ℚ.< δ → x ≈̄[ ε ℚ.+ δ ] y) → x ≈̄[ ε ] y
  ≈̄-closed {ε = ε} h = slack λ δ pos →
    ≈[]-mono (≤-reflexive (trans (+-assoc ε (½ ℚ.* δ) (½ ℚ.* δ)) (cong (ε ℚ.+_) (½*+½* δ))))
             (≈̄⇒≈ (h (½ ℚ.* δ) (0<½* pos)) (½ ℚ.* δ) (0<½* pos))

  ≈̄[0]⇔∼ᵃ : (x ≈̄[ 0ℚ ] y) ⇔ (x ∼ᵃ y)
  ≈̄[0]⇔∼ᵃ = mk⇔ (λ h δ pos → ≈[]-mono (≤-reflexive (+-identityˡ δ)) (≈̄⇒≈ h δ pos))
                (λ h → slack λ δ pos → ≈[]-mono (≤-reflexive (sym (+-identityˡ δ))) (h δ pos))

  ≈̄-resp-∼ᵃ : x′ ∼ᵃ x → y ∼ᵃ y′ → x ≈̄[ ε ] y → x′ ≈̄[ ε ] y′
  ≈̄-resp-∼ᵃ {ε = ε} l r h =
    Approximation.≈[]-mono closure (≤-reflexive (trans (+-identityʳ (0ℚ ℚ.+ ε)) (+-identityˡ ε)))
      (≈̄-trans (≈̄-trans (Equivalence.from ≈̄[0]⇔∼ᵃ l) h) (Equivalence.from ≈̄[0]⇔∼ᵃ r))

------------------------------------------------------------------------
-- The hybrid lemma

-- maurer2002 Lemma 5(i) along a chain of hybrids: the end points are within
-- the sum of the steps.
module _ {Obs : Set o} (A : Approximation Obs ℚ-ordered ℓa) where

  open Approximation A

  hybrid : {n : ℕ} (H : Fin (suc n) → Obs) (ε : Fin n → ℚ)
         → ((i : Fin n) → H (inject₁ i) ≈[ ε i ] H (suc i))
         → H zero ≈[ ∑[ i < n ] ε i ] H (fromℕ n)
  hybrid {zero}  H ε h = ≈[]-refl
  hybrid {suc n} H ε h = ≈[]-trans (h zero) (hybrid (H ∘ suc) (ε ∘ suc) (h ∘ suc))
