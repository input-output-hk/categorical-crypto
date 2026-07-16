{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Pointwise congruence of `Canonical.residual`.
--
-- Under `_≡_`, stdlib's `remove`/`punchOut` are opaque, so `residual b`
-- is only *pointwise* equal to `residual b'` when `b`, `b'` agree
-- pointwise.  `residual-pw-cong` supplies that pointwise equation; it is
-- consumed by `Word.canonW-resp-≈` and `LehmerRotate.canonW-cons-rotate`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.CanonicalProps where

open import Data.Nat.Base using (suc)
open import Data.Fin.Base using (Fin; suc)
open import Data.Fin.Patterns using (0F)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

private
  variable
    a : Level
    A : Set a

open import Data.Fin.Properties using (punchOut-cong)
open import Data.Fin.Base using (punchOut)

-- `punchOut` is congruent in both arguments (stdlib provides only the `j` half).
private
  punchOut-cong-both
    : ∀ {n} (i i' j j' : Fin (suc n))
        (ei : i ≡ i') (ej : j ≡ j')
        (p : i ≢ j) (p' : i' ≢ j')
    → punchOut p ≡ punchOut p'
  punchOut-cong-both i .i j j' refl ej _ _ = punchOut-cong i ej

residual-pw-cong
  : ∀ {n} (b b' : FinBij (suc n) (suc n))
  → (∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → ∀ i → residual b P.⟨$⟩ʳ i ≡ residual b' P.⟨$⟩ʳ i
residual-pw-cong b b' eq i =
  punchOut-cong-both _ _ _ _ (eq 0F) (eq (suc i)) _ _
