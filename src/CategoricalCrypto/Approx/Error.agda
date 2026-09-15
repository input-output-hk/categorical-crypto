{-# OPTIONS --safe --without-K #-}

-- What a CATEGORY of approximate spaces costs, on top of the ε/2 argument.
--
-- `UC.Approximate.ErrorAlgebra` is deliberately minimal — a zero, an addition,
-- an order, positivity and a halving, which is exactly what `∼ᵃ`'s transitivity
-- spends and no more.  Composition needs the errors to be an ordered monoid as
-- well: two zero-error identifications must compose back to zero error, a fixed
-- bound must survive a zero-error change of either endpoint, and a bound built
-- from two others must be weakenable in both arguments.  Those three are
-- `⊕-identityˡ`, `⊕-identityʳ` and `⊕-mono`, and they are what `Approx`'s hom
-- equality and every quantitative UC theorem downstream spend.
--
-- None of them is needed as an EQUATION: `⊑` in the one direction suffices
-- throughout, which is what keeps a lax or upper-bound model admissible (the
-- resource extension of `docs/quantitative-uc-setup-plan.typ` §7 needs that).
--
-- This is a separate record rather than four more `ErrorAlgebra` fields because
-- the ε/2 consumers (`UC.Environment.Approximate`, `UC.Family`) ask for the
-- smaller interface and are entitled to keep it.

open import Data.Rational.Properties
  using (+-identityʳ; +-identityˡ; +-mono-≤; ≤-refl; ≤-reflexive; ≤-trans)
open import Level using (Level; 0ℓ; suc; _⊔_)

open import CategoricalCrypto.UC.Approximate using (ErrorAlgebra; ℚ-errors)

module CategoricalCrypto.Approx.Error where

record OrderedErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
  field errors : ErrorAlgebra es ℓe

  open ErrorAlgebra errors public

  field
    ⊑-refl      : {ε : Error} → ε ⊑ ε
    ⊑-trans     : {ε δ γ : Error} → ε ⊑ δ → δ ⊑ γ → ε ⊑ γ
    ⊕-identityˡ : {ε : Error} → ε₀ ⊕ ε ⊑ ε
    ⊕-identityʳ : {ε : Error} → ε ⊕ ε₀ ⊑ ε
    ⊕-mono      : {ε ε′ δ δ′ : Error} → ε ⊑ ε′ → δ ⊑ δ′ → ε ⊕ δ ⊑ ε′ ⊕ δ′

ℚ-ordered : OrderedErrorAlgebra 0ℓ 0ℓ
ℚ-ordered = record
  { errors      = ℚ-errors
  ; ⊑-refl      = ≤-refl
  ; ⊑-trans     = ≤-trans
  ; ⊕-identityˡ = λ {ε} → ≤-reflexive (+-identityˡ ε)
  ; ⊕-identityʳ = λ {ε} → ≤-reflexive (+-identityʳ ε)
  ; ⊕-mono      = +-mono-≤
  }
