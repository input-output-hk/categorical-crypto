{-# OPTIONS --safe --without-K #-}

-- The two ways to forget an approximate space to a setoid.  The exact one,
-- `Approx.Space.F₀`, needs nothing of the errors; the all-positive one needs a
-- `Refinement` of them.
--
-- The two are NOT isomorphic: a space whose error balls are not closed has
-- points that no positive error separates and zero error does
-- (`Approx.Separating`).  That is why an exact bound must stay in `Approx`
-- rather than be asked to respect `F₊`'s coarser equality.
--
-- The relation level is spelled `es ⊔ ℓe ⊔ ℓb` because `∼ᵃ` quantifies over an
-- error and a positivity proof, and only at that shape do the two functors
-- share a target category.
-- The levels are module PARAMETERS because `⊔` is not invertible: `ℓb` is not
-- recoverable from `es ⊔ ℓe ⊔ ℓb` by unification.

open import Categories.Category.Instance.Setoids
open import Categories.Functor

open import Level
open import Relation.Binary.Bundles

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Forget
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe)
  (R : Refinement E) (c ℓb : Level) where

open import CategoricalCrypto.Approx.Space E

private module P (X : ApproxSpace c (es ⊔ ℓe ⊔ ℓb)) = AllPositive R (ApproxSpace.approx X)

⟦_⟧₀ ⟦_⟧₊ : ApproxSpace c (es ⊔ ℓe ⊔ ℓb) → Setoid c (es ⊔ ℓe ⊔ ℓb)
⟦_⟧₀ = zeroSetoid
⟦_⟧₊ = P.positiveSetoid

F₊ : Functor (Approx c (es ⊔ ℓe ⊔ ℓb)) (Setoids c (es ⊔ ℓe ⊔ ℓb))
F₊ = record
  { F₀ = ⟦_⟧₊
  ; F₁ = λ f → record
      { to = Nonexpansive.map f ; cong = λ h ε pos → Nonexpansive.preserves f (h ε pos) }
  ; identity     = λ {A} → P.zero⇒positive A (ApproxSpace.≈[]-refl A)
  ; homomorphism = λ {_} {_} {Z} → P.zero⇒positive Z (ApproxSpace.≈[]-refl Z)
  ; F-resp-≈     = λ {_} {B} e {x} → P.zero⇒positive B (e x)
  }
