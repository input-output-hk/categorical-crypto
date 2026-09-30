{-# OPTIONS --safe --without-K #-}

-- The two ways to forget an approximate space to a setoid
-- (`docs/quantitative-uc-setup-plan.typ` §3), and the comparison between them.
-- The exact one, `Approx.Space.F₀`, needs nothing of the errors; the
-- all-positive one needs a `Refinement` of them.
--
-- The comparison `forget` is the identity on carriers and is deliberately NOT
-- an isomorphism: a space whose error balls are not closed has points that no
-- positive error separates and zero error does (`Approx.Separating`).  That is
-- why an exact bound must stay in `Approx` rather than be asked to respect
-- `F₊`'s coarser equality.
--
-- The relation level is spelled `es ⊔ ℓe ⊔ ℓb` because `∼ᵃ` quantifies over an
-- error and a positivity proof, and only at that shape do the two functors
-- share a target category — which a natural transformation between them needs.
-- The levels are module PARAMETERS because `⊔` is not invertible: `ℓb` is not
-- recoverable from `es ⊔ ℓe ⊔ ℓb` by unification.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)
open import CategoricalCrypto.UC.Approximate using (module AllPositive; Refinement)

module CategoricalCrypto.Approx.Forget
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe)
  (R : Refinement (OrderedErrorAlgebra.errors E)) (c ℓb : Level) where

open import CategoricalCrypto.Approx.Space E

private module P (X : ApproxSpace c (es ⊔ ℓe ⊔ ℓb)) = AllPositive R (ApproxSpace.approx X)

⟦_⟧₀ ⟦_⟧₊ : ApproxSpace c (es ⊔ ℓe ⊔ ℓb) → Setoid c (es ⊔ ℓe ⊔ ℓb)
⟦_⟧₀ = zeroSetoid
⟦ X ⟧₊ = record
  { Carrier = ApproxSpace.Carrier X ; _≈_ = P._∼ᵃ_ X ; isEquivalence = P.∼ᵃ-isEquivalence X }

F₊ : Functor (Approx c (es ⊔ ℓe ⊔ ℓb)) (Setoids c (es ⊔ ℓe ⊔ ℓb))
F₊ = record
  { F₀ = ⟦_⟧₊
  ; F₁ = λ f → record
      { to = Nonexpansive.map f ; cong = λ h ε pos → Nonexpansive.preserves f (h ε pos) }
  ; identity     = λ {A} → P.zero⇒positive A (ApproxSpace.≈[]-refl A)
  ; homomorphism = λ {_} {_} {Z} → P.zero⇒positive Z (ApproxSpace.≈[]-refl Z)
  ; F-resp-≈     = λ {_} {B} e {x} → P.zero⇒positive B (e x)
  }

forget : NaturalTransformation (F₀ c (es ⊔ ℓe ⊔ ℓb)) F₊
forget = record
  { η = λ X → record { to = λ x → x ; cong = P.zero⇒positive X }
  ; commute     = λ {_} {Y} _ → P.zero⇒positive Y (ApproxSpace.≈[]-refl Y)
  ; sym-commute = λ {_} {Y} _ → P.zero⇒positive Y (ApproxSpace.≈[]-refl Y)
  }
