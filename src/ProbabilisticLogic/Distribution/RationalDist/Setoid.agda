{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext.Setoid

open import ProbabilisticLogic.Distribution.RationalDist

module ProbabilisticLogic.Distribution.RationalDist.Setoid where

instance
  MonadSetoid-Dist-ℚ : MonadSetoid Dist-ℚ
  MonadSetoid-Dist-ℚ = record
    { _≈ᴹ_             = _≈Mℚ_
    ; ≈ᴹ-isEquivalence = ≈Mℚ-isEquivalence
    ; >>=-cong         = λ {x = μ} {ν} {f} {g} → >>=ᴹ-cong {μ = μ} {ν} {f} {g}
    }

  MonadLawsSetoid-Dist-ℚ : MonadLawsSetoid Dist-ℚ
  MonadLawsSetoid-Dist-ℚ = record
    { >>=-identityˡ-≈ = λ {a = a} {h} → >>=ᴹ-identityˡ a h
    ; >>=-identityʳ-≈ = >>=ᴹ-identityʳ
    ; >>=-assoc-≈     = λ m {g} {h} → >>=ᴹ-assoc m g h
    }

  CommutativeMonadSetoid-Dist-ℚ : CommutativeMonadSetoid Dist-ℚ
  CommutativeMonadSetoid-Dist-ℚ = record
    { >>=-comm-≈ = λ {x = μ} {ν} → >>=ᴹ-comm μ ν (λ x y → return-ℚ (x ,′ y))
    }
