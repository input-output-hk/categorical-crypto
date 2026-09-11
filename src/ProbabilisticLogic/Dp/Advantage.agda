{-# OPTIONS --safe --without-K --guardedness #-}

-- Distinguishing advantage on `Dₚ Bool`, as a RELATION indexed by a rational
-- slack rather than a function into ℚ.
--
-- `Dₚ`'s termination mass is a supremum of the monotone family `cum n`, and the
-- layer never forms it (see `Dp`'s header: no lubs, no lower reals).  So there
-- is no `adv : Dₚ Bool → Dₚ Bool → ℚ` to write down, and an axiomatized one
-- would be uninhabited here.  What survives is `_≼ₚ_`'s own shape — every
-- budget of the left is matched at *some* budget of the right — relaxed by `ε`:
--
--     d ≈ₚ[ ε ] e   =   no budget separates the two masses by more than ε
--
-- which is symmetric by construction, adds along composition (`≈ₚ[]-trans`
-- carries `ε + δ`) and degenerates to `_≈ₚ_` at `ε = 0`.  Those three are
-- exactly the pseudometric laws the vanishing-advantage layer spends, so
-- nothing is lost by never naming the number.
--
-- BOTH verdict masses are compared, `Pr≤[ b ]` for either `b`, and that is the
-- proposal's §1 requirement (`docs/kb/frontier/15-probabilistic-uc-model.typ`):
-- observing only the `true`-mass identifies an implementation that answers
-- `false` with one that diverges, since divergence weighs 0 under either
-- indicator.  Comparing both retains the distinction while still identifying an
-- almost-surely terminating loop with an immediate return.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties as ℚP

open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Advantage where

private variable d e h d′ e′ : Dₚ Bool
                 ε δ : ℚ

-- The mass of verdict `b` reached within `n` steps.
Pr≤[_] : Bool → ℕ → Dₚ Bool → ℚ
Pr≤[ b ] n d = cum n d (indᵇ b)

-- The `true` reading alone, which is what a one-sided probability-of-event
-- statement asks for (`CategoricalCrypto.UC.Approximate.Mass`).
Pr≤ : ℕ → Dₚ Bool → ℚ
Pr≤ = Pr≤[ true ]

indᵇ-nn : (b : Bool) → NNF (indᵇ b)
indᵇ-nn true  true  = 0≤1ℚ
indᵇ-nn true  false = ≤-refl
indᵇ-nn false true  = ≤-refl
indᵇ-nn false false = 0≤1ℚ

-- The other verdict weighs nothing, which is what lets a construction that
-- answers it stand in for divergence (`UC.Seam.Extract`'s truncation).
indᵇ-not : (b : Bool) → indᵇ b (not b) ≡ 0ℚ
indᵇ-not true  = refl
indᵇ-not false = refl

Pr≤-mono : {n m : ℕ} (b : Bool) (d : Dₚ Bool) → n ≤ℕ m → Pr≤[ b ] n d ℚ.≤ Pr≤[ b ] m d
Pr≤-mono b d le = cum-mono le d (indᵇ b) (indᵇ-nn b)

infix 4 _≼ₚ[_]_ _≈ₚ[_]_

_≼ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≼ₚ[ ε ] e = (b : Bool) (n : ℕ) → Σ[ m ∈ ℕ ] (Pr≤[ b ] n d ℚ.≤ Pr≤[ b ] m e ℚ.+ ε)

_≈ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≈ₚ[ ε ] e = (d ≼ₚ[ ε ] e) × (e ≼ₚ[ ε ] d)

------------------------------------------------------------------------
-- The pseudometric laws

≼ₚ⇒≼ₚ[0] : d ≼ₚ e → d ≼ₚ[ 0ℚ ] e
≼ₚ⇒≼ₚ[0] {e = e} le b n =
  let m , bd = le (indᵇ b) (indᵇ-nn b) n
  in m , ≤-trans bd (≤-reflexive (sym (+-identityʳ (Pr≤[ b ] m e))))

≼ₚ[]-refl : d ≼ₚ[ 0ℚ ] d
≼ₚ[]-refl {d} = ≼ₚ⇒≼ₚ[0] (≼ₚ-refl d)

≼ₚ[]-mono : ε ℚ.≤ δ → d ≼ₚ[ ε ] e → d ≼ₚ[ δ ] e
≼ₚ[]-mono {ε} {δ} le h b n =
  let m , bd = h b n in m , ≤-trans bd (+-monoʳ-≤ (Pr≤[ b ] m _) le)

≼ₚ[]-trans : d ≼ₚ[ ε ] e → e ≼ₚ[ δ ] h → d ≼ₚ[ ε ℚ.+ δ ] h
≼ₚ[]-trans {ε = ε} {δ = δ} {h = h} p q b n =
  let m , bd = p b n
      i , cd = q b m
  in i , ≤-trans bd (≤-trans (+-monoˡ-≤ ε cd)
                             (≤-reflexive (shuffle (Pr≤[ b ] i h) δ ε)))
  where
  shuffle : ∀ x y z → (x ℚ.+ y) ℚ.+ z ≡ x ℚ.+ (z ℚ.+ y)
  shuffle x y z = trans (+-assoc x y z) (cong (x ℚ.+_) (+-comm y z))

-- The left and right ends can be replaced by `_≼ₚ_`-comparable ones; this is
-- how an observation is transported along the ambient hom equality.
≼ₚ[]-resp : d′ ≼ₚ d → e ≼ₚ e′ → d ≼ₚ[ ε ] e → d′ ≼ₚ[ ε ] e′
≼ₚ[]-resp {d′} {d} {e} {e′} {ε} l r p b n =
  let m , bl = l (indᵇ b) (indᵇ-nn b) n
      i , bd = p b m
      j , br = r (indᵇ b) (indᵇ-nn b) i
  in j , ≤-trans bl (≤-trans bd (+-monoˡ-≤ ε br))

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
≈ₚ[]-resp (dd , dd′) (ee , ee′) (p , q) =
  ≼ₚ[]-resp dd′ ee p , ≼ₚ[]-resp ee′ dd q
