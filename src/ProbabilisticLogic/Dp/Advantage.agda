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

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ℕ_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties as ℚP
  using (+-assoc; +-comm; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext using (0≤1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)
open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Advantage where

private variable d e h d′ e′ : Dₚ Bool
                 ε δ : ℚ

-- The verdict mass reached within `n` steps.
Pr≤ : ℕ → Dₚ Bool → ℚ
Pr≤ n d = cum n d bool→ℚ

ind-nn : NNF bool→ℚ
ind-nn true  = 0≤1ℚ
ind-nn false = ≤-refl

Pr≤-mono : {n m : ℕ} (d : Dₚ Bool) → n ≤ℕ m → Pr≤ n d ℚ.≤ Pr≤ m d
Pr≤-mono d le = cum-mono le d bool→ℚ ind-nn

infix 4 _≼ₚ[_]_ _≈ₚ[_]_

_≼ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≼ₚ[ ε ] e = (n : ℕ) → Σ[ m ∈ ℕ ] (Pr≤ n d ℚ.≤ Pr≤ m e ℚ.+ ε)

_≈ₚ[_]_ : Dₚ Bool → ℚ → Dₚ Bool → Set
d ≈ₚ[ ε ] e = (d ≼ₚ[ ε ] e) × (e ≼ₚ[ ε ] d)

------------------------------------------------------------------------
-- The pseudometric laws

≼ₚ⇒≼ₚ[0] : d ≼ₚ e → d ≼ₚ[ 0ℚ ] e
≼ₚ⇒≼ₚ[0] {e = e} le n =
  let m , b = le bool→ℚ ind-nn n
  in m , ≤-trans b (≤-reflexive (sym (+-identityʳ (Pr≤ m e))))

≼ₚ[]-refl : d ≼ₚ[ 0ℚ ] d
≼ₚ[]-refl {d} = ≼ₚ⇒≼ₚ[0] (≼ₚ-refl d)

≼ₚ[]-mono : ε ℚ.≤ δ → d ≼ₚ[ ε ] e → d ≼ₚ[ δ ] e
≼ₚ[]-mono {ε} {δ} le b n =
  let m , bd = b n in m , ≤-trans bd (+-monoʳ-≤ (Pr≤ m _) le)

≼ₚ[]-trans : d ≼ₚ[ ε ] e → e ≼ₚ[ δ ] h → d ≼ₚ[ ε ℚ.+ δ ] h
≼ₚ[]-trans {ε = ε} {δ = δ} {h = h} b c n =
  let m , bd = b n
      i , cd = c m
  in i , ≤-trans bd (≤-trans (+-monoˡ-≤ ε cd)
                             (≤-reflexive (shuffle (Pr≤ i h) δ ε)))
  where
  shuffle : ∀ x y z → (x ℚ.+ y) ℚ.+ z ≡ x ℚ.+ (z ℚ.+ y)
  shuffle x y z = trans (+-assoc x y z) (cong (x ℚ.+_) (+-comm y z))

-- The left and right ends can be replaced by `_≼ₚ_`-comparable ones; this is
-- how an observation is transported along the ambient hom equality.
≼ₚ[]-resp : d′ ≼ₚ d → e ≼ₚ e′ → d ≼ₚ[ ε ] e → d′ ≼ₚ[ ε ] e′
≼ₚ[]-resp {d′} {d} {e} {e′} {ε} l r b n =
  let m , bl = l bool→ℚ ind-nn n
      i , bd = b m
      j , br = r bool→ℚ ind-nn i
  in j , ≤-trans bl (≤-trans bd (+-monoˡ-≤ ε br))

≈ₚ⇒≈ₚ[0] : d ≈ₚ e → d ≈ₚ[ 0ℚ ] e
≈ₚ⇒≈ₚ[0] (le , el) = ≼ₚ⇒≼ₚ[0] le , ≼ₚ⇒≼ₚ[0] el

≈ₚ[]-refl : d ≈ₚ[ 0ℚ ] d
≈ₚ[]-refl {d} = ≈ₚ⇒≈ₚ[0] (≈ₚ-refl d)

≈ₚ[]-sym : d ≈ₚ[ ε ] e → e ≈ₚ[ ε ] d
≈ₚ[]-sym (le , el) = el , le

≈ₚ[]-mono : ε ℚ.≤ δ → d ≈ₚ[ ε ] e → d ≈ₚ[ δ ] e
≈ₚ[]-mono le (b , c) = ≼ₚ[]-mono le b , ≼ₚ[]-mono le c

≈ₚ[]-trans : d ≈ₚ[ ε ] e → e ≈ₚ[ δ ] h → d ≈ₚ[ ε ℚ.+ δ ] h
≈ₚ[]-trans {ε = ε} {δ = δ} (b , b′) (c , c′) =
  ≼ₚ[]-trans b c , ≼ₚ[]-mono (≤-reflexive (+-comm δ ε)) (≼ₚ[]-trans c′ b′)

≈ₚ[]-resp : d ≈ₚ d′ → e ≈ₚ e′ → d ≈ₚ[ ε ] e → d′ ≈ₚ[ ε ] e′
≈ₚ[]-resp (dd , dd′) (ee , ee′) (b , c) =
  ≼ₚ[]-resp dd′ ee b , ≼ₚ[]-resp ee′ dd c
